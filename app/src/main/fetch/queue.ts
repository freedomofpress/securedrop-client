import Queue from "better-queue";

import fs from "fs";
import path from "path";
import { Writable } from "stream";

import { BufferedWriter } from "./bufferedWriter";
import { DB } from "../database";
import {
  AuthedRequest,
  FetchStatus,
  ItemMetadata,
  ProxyRequest,
  ProxyStreamResponse,
} from "../../types";
import { proxyStreamRequest } from "../proxy";
import { Crypto, CryptoError, encryptedFilepath } from "../crypto";

export type ItemFetchTask = {
  id: string;
};

type DownloadResult = Buffer | string;

export class TaskQueue {
  db: DB;
  queue: Queue;
  authToken?: string;

  constructor(db: DB, overrideTaskFn?: (task: ItemFetchTask, db: DB) => void) {
    this.db = db;
    this.queue = createQueue(
      db,
      overrideTaskFn ? overrideTaskFn : this.process,
    );
  }

  getAuthToken(): string {
    return this.authToken ? this.authToken : "";
  }

  // Queries the database for all items that need to be downloaded and queues
  // up download tasks to be processed.
  queueFetches(message: AuthedRequest) {
    this.authToken = message.authToken;
    try {
      const itemsToProcess = this.db.getItemsToProcess();
      console.debug("Items to process: ", itemsToProcess);
      for (const itemUUID of itemsToProcess) {
        const task: ItemFetchTask = {
          id: itemUUID,
        };
        this.queue.push(task, (err, _result) => {
          if (err) {
            console.error("Error executing fetch download task: ", task, err);
            this.db.failDownload(task.id);
          }
        });
      }
    } catch (e) {
      console.error("Error queueing fetches: ", e);
    }
  }

  // Process each task by downloading item data via proxy, and then
  // decrypting data to plaintext stored in the DB or to a file on disk.
  process = async (item: ItemFetchTask, db: DB) => {
    console.debug("Processing item: ", item);

    const {
      data: metadata,
      fetch_status: status,
      fetch_progress: progress,
    } = db.getItem(item.id);

    // Skip items that are complete, terminally failed, paused, or not scheduled
    if (
      status == FetchStatus.Complete ||
      status == FetchStatus.FailedTerminal ||
      status == FetchStatus.Paused ||
      status == FetchStatus.NotScheduled
    ) {
      console.debug("Item task is not in an processable state, skipping...");
      return;
    }

    // Phase 1: Download
    let downloadResult: DownloadResult | undefined;
    let nextStatus = status;
    if (
      status === FetchStatus.Initial ||
      status === FetchStatus.DownloadInProgress ||
      status === FetchStatus.FailedDownloadRetryable
    ) {
      downloadResult = await this.download(item, db, metadata, progress || 0);
      nextStatus = FetchStatus.DecryptionInProgress;
    }

    // Phase 2: Decryption (or failed decryption retries)
    if (
      nextStatus === FetchStatus.DecryptionInProgress ||
      nextStatus === FetchStatus.FailedDecryptionRetryable
    ) {
      await this.decrypt(item, db, metadata, downloadResult);
    } else {
      // Handle unexpected statuses
      console.debug(
        `Unexpected status ${nextStatus} for item ${item.id}, skipping...`,
      );
    }
  };

  private async download(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    progress: number,
  ): Promise<DownloadResult> {
    console.debug(`Starting download for ${metadata.kind} ${item.id}`);
    db.setDownloadInProgress(item.id);

    let downloadFilePath: string = "";
    let downloadWriter: Writable;

    if (metadata.kind === "message" || metadata.kind === "reply") {
      // For messages/replies: use BufferedWriter (in-memory only)
      downloadWriter = new BufferedWriter();
    } else if (metadata.kind === "file") {
      // For files: write directly to disk
      downloadFilePath = encryptedFilepath(metadata.source, item.id);
      const downloadDir = path.dirname(downloadFilePath);
      await fs.promises.mkdir(downloadDir, { recursive: true });
      downloadWriter = fs.createWriteStream(downloadFilePath);
    } else {
      throw new Error(`Unsupported item kind: ${metadata.kind}`);
    }

    const queryPath = `/api/v1/sources/${metadata.source}/${metadata.kind == "reply" ? "replies" : "submissions"}/${item.id}/download`;
    const downloadRequest: ProxyRequest = {
      method: "GET",
      path_query: queryPath,
      headers: authHeader(this.getAuthToken()),
    };

    let downloadResponse = await proxyStreamRequest(
      downloadRequest,
      downloadWriter,
      progress,
    );

    // If we received JSON response, indicates an error from the server
    if ("data" in downloadResponse && downloadResponse.error) {
      db.failDownload(item.id);
      throw new Error(
        `Received error from server with status ${downloadResponse.status}: ${downloadResponse.data?.toString()}`,
      );
    }

    downloadResponse = downloadResponse as ProxyStreamResponse;

    if (!downloadResponse.complete) {
      const bytesWritten = progress + downloadResponse.bytesWritten;
      db.setDownloadInProgress(item.id, bytesWritten);
      db.failDownload(item.id);
      throw new Error(
        `Unable to complete stream download, wrote ${downloadResponse.bytesWritten} bytes: ${downloadResponse.error?.message}`,
      );
    }

    if (metadata.kind === "message" || metadata.kind === "reply") {
      return (downloadWriter as BufferedWriter).getBuffer();
    }
    return downloadFilePath;
  }

  private async decrypt(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    downloadResult?: DownloadResult,
  ) {
    const crypto = Crypto.getInstance();
    if (!crypto) {
      throw new Error("Crypto not initialized in fetch worker, cannot decrypt");
    }

    // Set status to decryption in progress
    db.setDecryptionInProgress(item.id);
    try {
      if (metadata.kind === "file") {
        await this.decryptFile(item, db, crypto, metadata);
        return;
      }
      if (downloadResult) {
        await this.decryptBuffer(
          item,
          db,
          crypto,
          metadata,
          downloadResult as Buffer,
        );
      } else {
        await this.decryptRetry(item, db, crypto, metadata);
      }
    } catch (error) {
      db.failDecryption(item.id);
      throw error;
    }
  }

  // Decrypt plaintext item from the in-memory buffer and persist to DB
  // on success. On failure, write the ciphertext to disk so we can retry
  // without needing to re-download.
  private async decryptBuffer(
    item: ItemFetchTask,
    db: DB,
    crypto: Crypto,
    metadata: ItemMetadata,
    buffer: Buffer,
  ) {
    try {
      const decryptedContent = await crypto.decryptMessage(buffer);

      // Store the decrypted plaintext and mark item as complete
      db.completePlaintextItem(item.id, decryptedContent);
    } catch (error) {
      if (error instanceof CryptoError) {
        console.warn(
          `Failed to decrypt ${metadata.kind} ${item.id}: ${error.message}`,
        );
      }
      // Ensure data is persisted to disk for retries
      try {
        const downloadFilePath = encryptedFilepath(metadata.source, item.id);
        const downloadDir = path.dirname(downloadFilePath);
        await fs.promises.mkdir(downloadDir, { recursive: true });
        await fs.promises.writeFile(downloadFilePath, buffer);
        console.debug(
          `Saved encrypted buffer data to disk for retry: ${downloadFilePath}`,
        );
      } catch (saveError) {
        console.warn(`Failed to save encrypted data to disk: ${saveError}`);
      }
      throw error;
    }
  }

  // Decrypt a formerly failed message or reply decryption. Reads the
  // ciphertext from disk to decrypt, and then write the plaintext to
  // DB on success and clean up the encrypted file.
  private async decryptRetry(
    item: ItemFetchTask,
    db: DB,
    crypto: Crypto,
    metadata: ItemMetadata,
  ) {
    const downloadPath = encryptedFilepath(metadata.source, item.id);
    try {
      const buffer = await fs.promises.readFile(downloadPath);
      const decryptedContent = await crypto.decryptMessage(buffer);

      // Store the decrypted plaintext and mark item as complete
      db.completePlaintextItem(item.id, decryptedContent);
    } catch (error) {
      throw new Error(`Failed to load encrypted data from disk: ${error}`);
    }

    // After successful decryption, clean up the encrypted file
    try {
      await fs.promises.unlink(downloadPath);
    } catch (error) {
      console.warn(`Failed to clean up encrypted file: ${error}`);
    }
  }

  // Decrypt an encrypted file submission. Writes the unencrypted filepath
  // to DB on success.
  private async decryptFile(
    item: ItemFetchTask,
    db: DB,
    crypto: Crypto,
    metadata: ItemMetadata,
  ) {
    const downloadPath = encryptedFilepath(metadata.source, item.id);
    try {
      const decryptedFilepath = await crypto.decryptFile(downloadPath);
      db.completeFileItem(
        item.id,
        path.join(decryptedFilepath.filePath, decryptedFilepath.filename),
      );
      console.debug(`Successfully decrypted ${metadata.kind} ${item.id}`);
    } catch (error) {
      if (error instanceof CryptoError) {
        console.warn(
          `Failed to decrypt ${metadata.kind} ${item.id}: ${error.message}`,
        );
      }
      throw error;
    }

    // After successful decryption, clean up the encrypted file
    try {
      await fs.promises.unlink(downloadPath);
    } catch (error) {
      console.warn(`Failed to clean up encrypted file: ${error}`);
    }
  }
}

function createQueue(
  db: DB,
  taskFn: (task: ItemFetchTask, db: DB) => void,
): Queue {
  const q: Queue = new Queue(
    async (task: ItemFetchTask, cb: Queue.ProcessFunctionCb<void>) => {
      try {
        await taskFn(task, db);
        cb();
      } catch (e) {
        cb(e);
      }
    },
    {
      batchSize: 1,
      maxTimeout: 60_000,
      maxRetries: 5,
      id: "id",
      // Merge handles tasks scheduled with the same ID
      // We want to simply allow the existing task to keep running
      // and treat the operation as idempotent
      merge: function (oldTask, _newTask, _cb) {
        return oldTask;
      },
      failTaskOnProcessException: true,
      autoResume: true,
    },
  );

  q.on("error", (error) => {
    console.error("Error from queue: ", error);
  });

  q.on("task_failed", (taskId, errorMessage) => {
    console.error(
      "Task failed and exceeded retry attempts, removing from queue: ",
      taskId,
      errorMessage,
    );
    db.terminallyFailItem(taskId);
  });

  return q;
}

function authHeader(authToken: string | undefined): Record<string, string> {
  return authToken
    ? {
        Accept: "application/json",
        "Content-Type": "application/json",
        Authorization: `Token ${authToken}`,
      }
    : {};
}
