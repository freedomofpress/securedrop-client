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
  bytes,
  ms,
} from "../../types";
import {
  proxyStreamRequest,
  MESSAGE_REPLY_DOWNLOAD_TIMEOUT_MS,
} from "../proxy";
import { Crypto, CryptoError } from "../crypto";
import { MessagePort } from "worker_threads";
import { Storage } from "../storage";

export type ItemFetchTask = {
  id: string;
};

type DownloadResult = Buffer | string;

export class TaskQueue {
  db: DB;
  messageQueue: Queue;
  fileQueue: Queue;
  authToken?: string;
  port?: MessagePort;
  storage: Storage;

  constructor(
    db: DB,
    port?: MessagePort,
    overrideTaskFn?: (task: ItemFetchTask, db: DB) => void,
  ) {
    this.db = db;
    this.messageQueue = createQueue(
      "message-queue",
      db,
      overrideTaskFn ? overrideTaskFn : this.process,
      // Max timeout: 60s for messages
      60_000,
      port,
    );
    this.fileQueue = createQueue(
      "file-queue",
      db,
      overrideTaskFn ? overrideTaskFn : this.process,
      // Max timeout per task attempt. For the maximum file size of 500MB, the
      // worst-case download timeout is ~4.2 hours (based on 50 KB/s over Tor).
      // We set this to 2 hours as a reasonable per-attempt limit, relying on the
      // 5 retries below to handle worst-case large file downloads. Each retry gets
      // a fresh timeout, so total potential time is 2 hours × 6 attempts = 12 hours.
      7_200_000, // 2 hours in milliseconds
      port,
    );
    this.port = port;
    this.storage = new Storage();
  }

  getAuthToken(): string {
    return this.authToken ? this.authToken : "";
  }

  // Calculate a realistic timeout in milliseconds based on the size of the download.
  // This scales the timeout per file so that it increases as the file size increases.
  //
  // Based on Tor metrics, reasonable estimations for download times over Tor:
  //   50 KiB  (51200 bytes)   =  6   seconds  (8,533 bytes/second)
  //   1  MiB  (1049000 bytes) =  15  seconds  (~69,905 bytes/second)
  //
  // For more information, see:
  // https://metrics.torproject.org/torperf.html?start=2022-12-06&end=2023-03-06&server=onion
  //
  // The timeout returned is larger than the expected download time to account for
  // network variability. We use 50,000 bytes/second instead of 69,905 bytes/second
  // and apply a 1.5x adjustment factor.
  //
  // Minimum timeout is 25 seconds.
  private getRealisticTimeout(size: bytes): ms {
    const TIMEOUT_BYTES_PER_SECOND = 50_000.0;
    const TIMEOUT_ADJUSTMENT_FACTOR = 1.5;
    const TIMEOUT_BASE = 25_000; // 25 seconds in milliseconds

    const timeout = Math.ceil(
      (size / TIMEOUT_BYTES_PER_SECOND) *
        TIMEOUT_ADJUSTMENT_FACTOR *
        1000,
    );
    return (timeout + TIMEOUT_BASE) as ms;
  }

  // Queries the database for all items that need to be downloaded and queues
  // up download tasks to be processed.
  // Routes items to the appropriate queue:
  // - Messages/replies go to messageQueue
  // - Files go to fileQueue
  // This allows messages to be fetched while files are downloading, since that
  // may be a long-running process
  queueFetches(message: AuthedRequest) {
    this.authToken = message.authToken;
    try {
      const itemsToProcess = this.db.getItemsToProcess();
      if (itemsToProcess.length > 0) {
        console.debug("Items to process: ", itemsToProcess);
      }
      for (const itemUUID of itemsToProcess) {
        const task: ItemFetchTask = {
          id: itemUUID,
        };

        const item = this.db.getItem(itemUUID);
        if (!item) {
          continue;
        }

        const queue =
          item.data.kind === "file" ? this.fileQueue : this.messageQueue;

        queue.push(task, (err, _result) => {
          if (err) {
            console.error(
              `Error executing fetch download task in queue: `,
              task,
              err,
            );
            this.db.failDownload(task.id);
            if (this.port) {
              this.port.postMessage(this.db.getItem(task.id));
            }
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
    try {
      console.debug("Processing item: ", item);

      const dbItem = db.getItem(item.id);
      if (!dbItem) {
        console.debug("Item not found");
        return;
      }

      const {
        data: metadata,
        fetch_status: status,
        fetch_progress: progress,
      } = dbItem;

      // Skip items that are complete, terminally failed, paused, or not scheduled
      if (
        status == FetchStatus.Complete ||
        status == FetchStatus.FailedTerminal ||
        status == FetchStatus.Paused
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

      // After decryption, update source message preview and
      // post message to main thread
      if (this.port) {
        this.port.postMessage(this.db.getSource(metadata.source));
      }
    } finally {
      // After every process tick, post message to main thread
      if (this.port) {
        this.port.postMessage(this.db.getItem(item.id));
      }
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
      downloadFilePath = this.storage.downloadFilePath(metadata, item);
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

    // Calculate timeout based on item type
    let timeout: ms;
    if (metadata.kind === "message" || metadata.kind === "reply") {
      // Messages and replies use fixed 20 second timeout
      timeout = MESSAGE_REPLY_DOWNLOAD_TIMEOUT_MS;
    } else {
      // Files use dynamic timeout based on size
      timeout = this.getRealisticTimeout(metadata.size as bytes);
    }

    console.debug(
      `Downloading ${metadata.kind} ${item.id} (size: ${metadata.size} bytes) with timeout: ${timeout}ms`,
    );

    // Progress callback to update database and notify renderer during download
    // Throttle updates to avoid overwhelming the UI (max once per 200ms)
    let lastProgressUpdate = 0;
    const PROGRESS_UPDATE_INTERVAL_MS = 200;

    const onProgress = (bytesWritten: number) => {
      const now = Date.now();
      const totalBytesWritten = progress + bytesWritten;

      // Always update the database with current progress
      db.setDownloadInProgress(item.id, totalBytesWritten);

      // Throttle UI updates to avoid overwhelming the renderer
      if (
        this.port &&
        now - lastProgressUpdate >= PROGRESS_UPDATE_INTERVAL_MS
      ) {
        lastProgressUpdate = now;
        this.port.postMessage(db.getItem(item.id));
      }
    };

    let downloadResponse = await proxyStreamRequest(
      downloadRequest,
      downloadWriter,
      progress,
      undefined, // abortSignal
      timeout,
      onProgress,
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
        const downloadFilePath = this.storage.downloadFilePath(metadata, item);
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
    const downloadPath = this.storage.downloadFilePath(metadata, item);
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
    const downloadPath = this.storage.downloadFilePath(metadata, item);
    const itemDirectory = this.storage.itemDirectory(metadata);
    try {
      const finalAbsolutePath = await crypto.decryptFile(
        this.storage,
        itemDirectory,
        downloadPath,
      );
      // Get the decrypted file size to display to the user
      const fileStats = await fs.promises.stat(finalAbsolutePath);
      const decryptedSize = fileStats.size;
      db.completeFileItem(item.id, finalAbsolutePath, decryptedSize);
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
  name: string,
  db: DB,
  taskFn: (task: ItemFetchTask, db: DB) => void,
  maxTimeout: number,
  port?: MessagePort,
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
      maxTimeout: maxTimeout,
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
    console.error(`Error from ${name}: `, error);
  });

  q.on("task_failed", (taskId, errorMessage) => {
    console.error(
      `Task failed and exceeded retry attempts in ${name}, removing from queue: `,
      taskId,
      errorMessage,
    );
    db.terminallyFailItem(taskId);
    if (port) {
      port.postMessage(db.getItem(taskId));
    }
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
