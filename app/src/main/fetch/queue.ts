import Queue from "better-queue";

import fs from "fs";
import os from "os";
import path from "path";
import { Writable } from "stream";

import { BufferedWriter } from "./bufferedWriter";
import { DB } from "../database";
import {
  FetchDownloadsMessage,
  FetchStatus,
  ItemMetadata,
  ProxyRequest,
  ProxyStreamResponse,
} from "../../types";
import { proxyStreamRequest } from "../proxy";
import { Crypto, CryptoError } from "../crypto";

export type ItemFetchTask = {
  id: string;
};

export class TaskQueue {
  db: DB;
  queue: Queue;
  authToken?: string;

  constructor(db: DB, overrideTaskFn?: (task: ItemFetchTask, db: DB) => void) {
    this.db = db;
    this.queue = createQueue(
      db,
      overrideTaskFn ? overrideTaskFn : this.fetchDownload,
    );
  }

  getAuthToken(): string {
    return this.authToken ? this.authToken : "";
  }

  // Queries the database for all items that need to be downloaded and queues
  // up download tasks to be processed.
  queueFetches(message: FetchDownloadsMessage) {
    this.authToken = message.authToken;
    try {
      const itemsToProcess = this.db.getItemsToProcess();
      console.log("Items to process: ", itemsToProcess);
      for (const itemUUID of itemsToProcess) {
        const task: ItemFetchTask = {
          id: itemUUID,
        };
        this.queue.push(task, (err, _result) => {
          if (err) {
            console.log("Error executing fetch download task: ", task, err);
            this.db.failDownload(task.id);
          }
        });
      }
    } catch (e) {
      console.log("Error queueing fetches: ", e);
    }
  }

  private getEncryptedFilePath(
    item: ItemFetchTask,
    metadata: ItemMetadata,
  ): string {
    return path.join(
      os.tmpdir(),
      "download",
      metadata.source,
      item.id,
      "encrypted.gpg",
    );
  }

  fetchDownload = async (item: ItemFetchTask, db: DB) => {
    console.log("Processing item: ", item);

    const [metadata, status, progress] = db.getItemWithFetchStatus(item.id);

    // Skip items that are already complete, terminally failed, or paused
    if (
      status == FetchStatus.Complete ||
      status == FetchStatus.FailedTerminal ||
      status == FetchStatus.Paused
    ) {
      console.log("Item task is not in an processable state, skipping...");
      return;
    }

    // Phase 1: Download
    if (
      status === FetchStatus.Initial ||
      status === FetchStatus.FailedDownloadRetryable
    ) {
      await this.performDownloadAndDecryption(item, db, metadata, progress);
      return;
    }

    // Phase 2: Decryption (for failed decryption retries)
    if (status === FetchStatus.FailedDecryptionRetryable) {
      await this.performDecryption(item, db, metadata);
      return;
    }

    // Handle unexpected statuses
    console.log(`Unexpected status ${status} for item ${item.id}, skipping...`);
  };

  private async performDownloadAndDecryption(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    progress: number,
  ) {
    console.log(`Starting download phase for ${metadata.kind} ${item.id}`);

    // Set status to download in progress
    db.setDownloadInProgress(item.id);

    let downloadFilePath: string = "";
    let downloadWriter: Writable;

    if (metadata.kind === "message" || metadata.kind === "reply") {
      // For messages/replies: use BufferedWriter (in-memory only)
      downloadWriter = new BufferedWriter();
    } else if (metadata.kind === "file") {
      // For files: write directly to disk
      downloadFilePath = this.getEncryptedFilePath(item, metadata);
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

    console.log("Proxying request to: ", downloadRequest);
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

    console.log(`Download completed for ${metadata.kind} ${item.id}`);

    // Move to decryption phase for messages/replies, complete for files
    if (metadata.kind === "message" || metadata.kind === "reply") {
      // For messages/replies: attempt decryption directly from BufferedWriter
      await this.performDecryption(
        item,
        db,
        metadata,
        downloadWriter as BufferedWriter,
      );
    } else {
      // TODO: we need to decrypt files as well
      db.completeFileItem(item.id, downloadFilePath);
    }
  }

  private async performDecryption(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    bufferWriter?: BufferedWriter,
  ) {
    console.log(`Starting decryption phase for ${metadata.kind} ${item.id}`);

    // Set status to decryption in progress
    db.setDecryptionInProgress(item.id);

    let encryptedData: Buffer;

    if (bufferWriter) {
      // First-time decryption after download
      const bufferResult = bufferWriter.getBuffer();
      if (bufferResult instanceof Error) {
        db.failDecryption(item.id);
        throw new Error(
          `Failed to get buffer from stream: ${bufferResult.message}`,
        );
      }
      encryptedData = bufferResult;
    } else {
      // Retry decryption from disk
      const downloadFilePath = this.getEncryptedFilePath(item, metadata);

      try {
        encryptedData = await fs.promises.readFile(downloadFilePath);
        console.log(
          `Loaded encrypted data from disk for retry: ${downloadFilePath}`,
        );
      } catch (error) {
        db.failDecryption(item.id);
        throw new Error(`Failed to load encrypted data from disk: ${error}`);
      }
    }

    try {
      // Decrypt the message/reply content
      const crypto = Crypto.getInstance();
      if (!crypto) {
        throw new Error("Crypto not initialized in fetch worker");
      }

      const decryptedContent = await crypto.decryptMessage(encryptedData);

      // Store the decrypted plaintext and mark as complete
      db.completePlaintextItem(item.id, decryptedContent);
      console.log(
        `Successfully decrypted ${metadata.kind} ${item.id} via fetch queue`,
      );

      // Clean up encrypted file after successful decryption (only if it exists - retry case)
      if (!bufferWriter) {
        const downloadFilePath = this.getEncryptedFilePath(item, metadata);
        try {
          await fs.promises.unlink(downloadFilePath);
          console.log(`Cleaned up encrypted file: ${downloadFilePath}`);
        } catch (error) {
          console.warn(`Failed to clean up encrypted file: ${error}`);
        }
      }
    } catch (error) {
      if (error instanceof CryptoError) {
        console.error(
          `Failed to decrypt ${metadata.kind} ${item.id}: ${error.message}`,
        );

        // For first-time decryption failure, ensure data is saved to disk
        if (bufferWriter) {
          const downloadFilePath = this.getEncryptedFilePath(item, metadata);
          try {
            const bufferResult = bufferWriter.getBuffer();
            if (!(bufferResult instanceof Error)) {
              const downloadDir = path.dirname(downloadFilePath);
              await fs.promises.mkdir(downloadDir, { recursive: true });
              await fs.promises.writeFile(downloadFilePath, bufferResult);
              console.log(
                `Saved encrypted data to disk for retry: ${downloadFilePath}`,
              );
            }
          } catch (saveError) {
            console.error(
              `Failed to save encrypted data to disk: ${saveError}`,
            );
          }
        }

        db.failDecryption(item.id);
        throw new Error(`Decryption failed: ${error.message}`);
      } else {
        db.failDecryption(item.id);
        throw error;
      }
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
    console.log("Error from queue: ", error);
  });

  q.on("task_failed", (taskId, errorMessage) => {
    console.log(
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
