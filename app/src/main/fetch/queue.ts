import Queue from "better-queue";

import { createHash } from "node:crypto";
import fs from "fs";
import path from "path";
import { Writable } from "stream";

import { BufferedWriter } from "./bufferedWriter";
import { DB } from "../database";
import { getRealisticTimeout } from "../timeouts";
import {
  AuthedRequest,
  FetchStatus,
  ItemMetadata,
  NONPROCESSABLE_FETCH_STATUSES,
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

// Thrown when a download is intentionally aborted (paused or cancelled by the user).
// This is not an error condition and should not cause the item to be marked as failed.
class DownloadCancelledError extends Error {
  constructor() {
    super("Download was cancelled");
  }
}

const MESSAGE_QUEUE_BATCH_LIMIT = 25;
const FILE_QUEUE_BATCH_LIMIT = 2;

export class TaskQueue {
  db: DB;
  messageQueue: Queue;
  fileQueue: Queue;
  authToken?: string;
  port?: MessagePort;
  storage: Storage;
  activeDownloads = new Map<
    string,
    { sourceUuid: string; controller: AbortController }
  >();
  activeDecryptions = new Map<
    string,
    { sourceUuid: string; controller: AbortController }
  >();

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

    // After each completed or terminally-failed task, try to top up the
    // queue from the database so large backlogs drain without waiting for
    // the next sync tick.
    const refill = () => this.refillQueues();
    this.messageQueue.on("task_finish", refill);
    this.messageQueue.on("task_failed", refill);
    this.fileQueue.on("task_finish", refill);
    this.fileQueue.on("task_failed", refill);
  }

  getAuthToken(): string {
    return this.authToken ? this.authToken : "";
  }

  // Aborts any in-progress download for the given item.
  cancelDownload(itemId: string) {
    const entry = this.activeDownloads.get(itemId);
    if (entry) {
      entry.controller.abort();
    }
  }

  abortSourceFetch(sourceUuid: string) {
    console.debug(
      "Source has been deleted: aborting downloads + decryptions: ",
      sourceUuid,
    );
    for (const [itemId, entry] of this.activeDownloads) {
      if (entry.sourceUuid === sourceUuid) {
        entry.controller.abort();
        this.activeDownloads.delete(itemId);
      }
    }
    for (const [itemId, entry] of this.activeDecryptions) {
      if (entry.sourceUuid === sourceUuid) {
        entry.controller.abort();
        this.activeDecryptions.delete(itemId);
      }
    }
  }

  private refillQueues() {
    if (!this.authToken) {
      return;
    }
    this.queueFetches({ authToken: this.authToken });
  }

  // Check that item is still in processable state: not cancelled, paused
  // complete, or scheduled for deletion
  private isProcessable(itemId: string, db: DB): boolean {
    const item = db.getItem(itemId);
    return (
      item !== null &&
      item?.fetch_status !== undefined &&
      !NONPROCESSABLE_FETCH_STATUSES.has(item.fetch_status)
    );
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
      const itemsToProcess = this.db.getItemsToProcess({
        messageLimit: MESSAGE_QUEUE_BATCH_LIMIT,
        fileLimit: FILE_QUEUE_BATCH_LIMIT,
      });
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
            try {
              this.db.failDownload(task.id);
            } catch (failError) {
              console.error(
                `Error failing download in queue callback for item ${task.id}:`,
                failError,
              );
            }
            if (this.port) {
              try {
                this.port.postMessage(this.db.getItem(task.id));
              } catch (postError) {
                console.error(
                  `Error posting queue callback update for item ${task.id}:`,
                  postError,
                );
              }
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
      console.log("Processing item: ", item);

      // Skip items that are complete, terminally failed, paused, cancelled,
      // scheduled for deletion, or otherwise not in a processable state.
      const dbItem = db.getItem(item.id);
      if (
        !dbItem ||
        dbItem.fetch_status === undefined ||
        NONPROCESSABLE_FETCH_STATUSES.has(dbItem.fetch_status)
      ) {
        console.debug("Item task is not in a processable state, skipping...");
        return;
      }

      const {
        data: metadata,
        fetch_status: status,
        fetch_progress: progress,
      } = dbItem;

      // Phase 1: Download
      let downloadResult: DownloadResult | undefined;
      let nextStatus = status;
      if (
        status === FetchStatus.Initial ||
        status === FetchStatus.DownloadInProgress ||
        status === FetchStatus.FailedDownloadRetryable
      ) {
        try {
          downloadResult = await this.download(
            item,
            db,
            metadata,
            progress || 0,
          );
        } catch (e) {
          if (e instanceof DownloadCancelledError) {
            // Download was intentionally paused or cancelled — not a failure
            return;
          }
          throw e;
        }
        nextStatus = FetchStatus.DecryptionInProgress;
      }

      // Re-check: if the item was marked for deletion during download, stop.
      if (!this.isProcessable(item.id, db)) {
        console.debug(
          `Item ${item.id} in non-processable state after download, skipping decryption...`,
        );
        return;
      }

      // Phase 2: Decryption (or failed decryption retries)
      if (
        nextStatus === FetchStatus.DecryptionInProgress ||
        nextStatus === FetchStatus.FailedDecryptionRetryable
      ) {
        try {
          await this.decrypt(item, db, metadata, downloadResult);
        } catch (e) {
          if (e instanceof DownloadCancelledError) {
            // Decryption was intentionally aborted — not a failure
            return;
          }
          throw e;
        }
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

  private async prepareDownload(
    item: ItemFetchTask,
    metadata: ItemMetadata,
    progress: number,
  ): Promise<{ path: string; writer: Writable; progress: number }> {
    let downloadFilePath: string = "";
    let downloadWriter: Writable;
    let resumeProgress = 0;

    if (metadata.kind === "message" || metadata.kind === "reply") {
      // For messages/replies: use BufferedWriter (in-memory only)
      downloadWriter = new BufferedWriter();
    } else if (metadata.kind === "file") {
      // For files: write directly to disk
      downloadFilePath = this.storage.downloadFilePath(metadata, item);
      const downloadDir = path.dirname(downloadFilePath);
      await fs.promises.mkdir(downloadDir, { recursive: true });
      if (progress > 0) {
        // Re-read the resume position from disk — it's the source of truth,
        // in case the DB is out of sync with what was actually written.
        try {
          const stats = await fs.promises.stat(downloadFilePath);
          resumeProgress = stats.size;
        } catch (error: unknown) {
          if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
            throw error;
          }
          // File doesn't exist, start from the beginning
        }
      }
      // If we have some progress to resume, append from where the file ends,
      // otherwise truncate and start anew.
      downloadWriter = fs.createWriteStream(downloadFilePath, {
        flags: resumeProgress > 0 ? "a" : "w",
      });
    } else {
      throw new Error(`Unsupported item kind: ${metadata.kind}`);
    }
    return {
      path: downloadFilePath,
      writer: downloadWriter,
      progress: resumeProgress,
    };
  }

  private async download(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    progress: number,
  ): Promise<DownloadResult> {
    console.debug(`Starting download for ${metadata.kind} ${item.id}`);
    const abortController = new AbortController();
    this.activeDownloads.set(item.id, {
      sourceUuid: metadata.source,
      controller: abortController,
    });
    try {
      db.startDownloadInProgress(item.id);
      return await this.innerDownload(
        item,
        db,
        metadata,
        progress,
        abortController,
      );
    } finally {
      this.activeDownloads.delete(item.id);
    }
  }

  private async innerDownload(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    originalProgress: number,
    abortController: AbortController,
  ): Promise<DownloadResult> {
    const {
      path: downloadFilePath,
      writer: downloadWriter,
      progress,
    } = await this.prepareDownload(item, metadata, originalProgress);

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
      timeout = getRealisticTimeout(metadata.size as bytes);
    }

    console.log(
      `Downloading ${metadata.kind} ${item.id} (size: ${metadata.size} bytes) with timeout: ${timeout}ms`,
    );

    // Progress callback to update database and notify renderer during download
    // Throttle updates to avoid overwhelming the UI (max once per 200ms)
    let lastProgressUpdate = 0;
    const PROGRESS_UPDATE_INTERVAL_MS = 200;

    const onProgress = (bytesWritten: number) => {
      const now = Date.now();
      const totalBytesWritten = progress + bytesWritten;

      // Don't override the DB status if the download has been cancelled
      if (!abortController.signal.aborted) {
        if (!db.updateDownloadInProgress(item.id, totalBytesWritten)) {
          return;
        }
      }

      // Throttle UI updates to avoid overwhelming the renderer
      if (
        this.port &&
        now - lastProgressUpdate >= PROGRESS_UPDATE_INTERVAL_MS
      ) {
        lastProgressUpdate = now;
        this.port.postMessage(db.getItem(item.id));
      }
    };

    let downloadResponse;
    try {
      downloadResponse = await proxyStreamRequest(
        downloadRequest,
        downloadWriter,
        progress,
        abortController.signal,
        timeout,
        onProgress,
      );
    } catch (e) {
      if (abortController.signal.aborted) {
        throw new DownloadCancelledError();
      }
      throw e;
    }

    // If we received JSON response, indicates an error from the server
    if ("data" in downloadResponse && downloadResponse.error) {
      db.failDownload(item.id);
      throw new Error(
        `Received error from server with status ${downloadResponse.status}: ${downloadResponse.data?.toString()}`,
      );
    }

    downloadResponse = downloadResponse as ProxyStreamResponse;

    if (!downloadResponse.complete) {
      // If the abort signal was triggered, the download was intentionally
      // stopped by the user (pause or cancel) — don't mark the item as failed
      if (abortController.signal.aborted) {
        throw new DownloadCancelledError();
      }

      const bytesWritten = progress + downloadResponse.bytesWritten;
      db.updateDownloadInProgress(item.id, bytesWritten);
      db.failDownload(item.id);
      throw new Error(
        `Unable to complete stream download, wrote ${downloadResponse.bytesWritten} bytes: ${downloadResponse.error?.message}`,
      );
    }

    await this.verifyEtag(
      item,
      db,
      metadata,
      downloadResponse.sha256sum,
      downloadWriter,
      downloadFilePath,
    );

    if (metadata.kind === "message" || metadata.kind === "reply") {
      return (downloadWriter as BufferedWriter).getBuffer();
    }
    return downloadFilePath;
  }

  // Verify ETag checksum for transport integrity purposes, otherwise fail terminally
  private async verifyEtag(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    etagRaw: string | undefined,
    downloadWriter: Writable,
    downloadFilePath: string,
  ): Promise<void> {
    if (!etagRaw) {
      db.terminallyFailItem(item.id);
      throw new Error(`Missing ETag checksum for ${metadata.kind} ${item.id}`);
    }
    const colonIdx = etagRaw.indexOf(":");
    if (colonIdx === -1 || etagRaw.slice(0, colonIdx) !== "sha256") {
      db.terminallyFailItem(item.id);
      throw new Error(
        `Invalid or unsupported ETag format for ${metadata.kind} ${item.id}: ${etagRaw}`,
      );
    }
    const expectedHex = etagRaw.slice(colonIdx + 1);

    const hash = createHash("sha256");
    if (metadata.kind === "message" || metadata.kind === "reply") {
      hash.update((downloadWriter as BufferedWriter).getBuffer());
    } else {
      // Stream the file to avoid loading a large file entirely into memory
      const readStream = fs.createReadStream(downloadFilePath);
      for await (const chunk of readStream) {
        hash.update(chunk);
      }
    }
    const actualHash = hash.digest("hex");

    if (actualHash !== expectedHex) {
      db.terminallyFailItem(item.id);
      throw new Error(
        `ETag checksum mismatch for ${metadata.kind} ${item.id}: expected ${expectedHex}, got ${actualHash}`,
      );
    }
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

    const abortController = new AbortController();
    this.activeDecryptions.set(item.id, {
      sourceUuid: metadata.source,
      controller: abortController,
    });

    // Set status to decryption in progress
    db.setDecryptionInProgress(item.id);
    try {
      if (metadata.kind === "file") {
        await this.decryptFile(
          item,
          db,
          crypto,
          metadata,
          abortController.signal,
        );
        return;
      }
      if (downloadResult) {
        await this.decryptBuffer(
          item,
          db,
          crypto,
          metadata,
          downloadResult as Buffer,
          abortController.signal,
        );
      } else {
        await this.decryptRetry(
          item,
          db,
          crypto,
          metadata,
          abortController.signal,
        );
      }
    } catch (error) {
      if ((error as Error).name === "AbortError") {
        throw new DownloadCancelledError();
      }
      db.failDecryption(item.id);
      throw error;
    } finally {
      this.activeDecryptions.delete(item.id);
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
    signal?: AbortSignal,
  ) {
    try {
      const decryptedContent = await crypto.decryptMessage(buffer, signal);

      // Re-check: if the item was deleted during decryption, drop the result
      if (!this.isProcessable(item.id, db)) {
        return;
      }

      // Store the decrypted plaintext and mark item as complete
      db.completePlaintextItem(item.id, decryptedContent);
    } catch (error) {
      // Don't save to disk if the decryption was intentionally aborted
      if ((error as Error).name !== "AbortError") {
        if (error instanceof CryptoError) {
          console.warn(
            `Failed to decrypt ${metadata.kind} ${item.id}: ${error.message}`,
          );
        }
        // Ensure data is persisted to disk for retries
        try {
          const downloadFilePath = this.storage.downloadFilePath(
            metadata,
            item,
          );
          const downloadDir = path.dirname(downloadFilePath);
          await fs.promises.mkdir(downloadDir, { recursive: true });
          await fs.promises.writeFile(downloadFilePath, buffer);
          console.debug(
            `Saved encrypted buffer data to disk for retry: ${downloadFilePath}`,
          );
        } catch (saveError) {
          console.warn(`Failed to save encrypted data to disk: ${saveError}`);
        }
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
    signal?: AbortSignal,
  ) {
    const downloadPath = this.storage.downloadFilePath(metadata, item);
    try {
      const buffer = await fs.promises.readFile(downloadPath);
      const decryptedContent = await crypto.decryptMessage(buffer, signal);

      // Re-check: if the item was deleted during decryption, drop the result
      if (!this.isProcessable(item.id, db)) {
        return;
      }

      // Store the decrypted plaintext and mark item as complete
      db.completePlaintextItem(item.id, decryptedContent);
    } catch (error) {
      if ((error as Error).name === "AbortError") {
        throw error;
      }
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
    signal?: AbortSignal,
  ) {
    const downloadPath = this.storage.downloadFilePath(metadata, item);
    const itemDirectory = this.storage.itemDirectory(metadata);
    try {
      const finalAbsolutePath = await crypto.decryptFile(
        this.storage,
        itemDirectory,
        downloadPath,
        signal,
      );

      // Re-check: if the item was deleted during decryption, drop the result
      if (!this.isProcessable(item.id, db)) {
        try {
          await fs.promises.unlink(finalAbsolutePath);
        } catch (error) {
          console.warn(
            `Failed to clean up decrypted file after deletion: ${error}`,
          );
        }
        return;
      }

      // Get the decrypted file size to display to the user
      const fileStats = await fs.promises.stat(finalAbsolutePath);
      const decryptedSize = fileStats.size;
      db.completeFileItem(item.id, finalAbsolutePath, decryptedSize);
      console.log(`Successfully decrypted ${metadata.kind} ${item.id}`);
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
    try {
      db.terminallyFailItem(taskId);
    } catch (failError) {
      console.error(
        `Error terminally failing item ${taskId} in ${name}:`,
        failError,
      );
    }
    if (port) {
      try {
        port.postMessage(db.getItem(taskId));
      } catch (postError) {
        console.error(
          `Error posting task_failed update for item ${taskId} in ${name}:`,
          postError,
        );
      }
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
