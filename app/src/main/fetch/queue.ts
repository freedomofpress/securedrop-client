import Queue from "better-queue";

import { createHash } from "node:crypto";
import fs from "fs";
import path from "path";
import { Writable } from "stream";

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

// Thrown when a download is intentionally aborted (paused or cancelled by the user).
// This is not an error condition and should not cause the item to be marked as failed.
class DownloadCancelledError extends Error {
  constructor() {
    super("Download was cancelled");
  }
}

const MESSAGE_QUEUE_BATCH_LIMIT = 25;
const FILE_QUEUE_BATCH_LIMIT = 2;

// Statuses handled by the download queues.
const DOWNLOAD_STATUSES = new Set<FetchStatus>([
  FetchStatus.Initial,
  FetchStatus.DownloadInProgress,
  FetchStatus.FailedDownloadRetryable,
]);

// Statuses handled by the decrypt queues.
const DECRYPT_STATUSES = new Set<FetchStatus>([
  FetchStatus.DecryptionInProgress,
  FetchStatus.FailedDecryptionRetryable,
]);

export class TaskQueue {
  db: DB;
  messageDownloadQueue: Queue;
  messageDecryptQueue: Queue;
  fileDownloadQueue: Queue;
  fileDecryptQueue: Queue;
  authToken: string | null = null;
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

  constructor(db: DB, port?: MessagePort) {
    this.db = db;
    this.messageDownloadQueue = createQueue(
      "message-download",
      db,
      this.processDownload,
      // Max timeout: 60s for messages
      60_000,
      port,
    );
    this.messageDecryptQueue = createQueue(
      "message-decrypt",
      db,
      this.processDecrypt,
      // Max timeout: 60s for messages
      60_000,
      port,
    );
    this.fileDownloadQueue = createQueue(
      "file-download",
      db,
      this.processDownload,
      // Max timeout per task attempt. For the maximum file size of 500MB, the
      // worst-case download timeout is ~4.2 hours (based on 50 KB/s over Tor).
      // We set this to 2 hours as a reasonable per-attempt limit, relying on the
      // 5 retries below to handle worst-case large file downloads. Each retry gets
      // a fresh timeout, so total potential time is 2 hours × 6 attempts = 12 hours.
      7_200_000, // 2 hours in milliseconds
      port,
    );
    this.fileDecryptQueue = createQueue(
      "file-decrypt",
      db,
      this.processDecrypt,
      // Max timeout: 1 hour — file decryption can be slow for large files
      3_600_000,
      port,
    );
    this.port = port;
    this.storage = new Storage();

    // After each completed or terminally-failed task, try to top up the
    // queues from the database so large backlogs drain without waiting for
    // the next sync tick.
    const refill = () => this.refillQueues();
    this.messageDownloadQueue.on("task_finish", refill);
    this.messageDownloadQueue.on("task_failed", refill);
    this.messageDecryptQueue.on("task_finish", refill);
    this.messageDecryptQueue.on("task_failed", refill);
    this.fileDownloadQueue.on("task_finish", refill);
    this.fileDownloadQueue.on("task_failed", refill);
    this.fileDecryptQueue.on("task_finish", refill);
    this.fileDecryptQueue.on("task_failed", refill);
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
    this.queueFetchesInner();
  }

  // Check that item is still in processable state: not cancelled, paused
  // complete, or scheduled for deletion
  private isProcessable(itemId: string, db: DB): boolean {
    const item = db.getItem(itemId);
    return (
      item !== null &&
      item.fetch_status !== null &&
      !NONPROCESSABLE_FETCH_STATUSES.has(item.fetch_status)
    );
  }

  queueFetches(message: AuthedRequest) {
    this.authToken = message.authToken;
    this.queueFetchesInner();
  }

  // Queries the database for all items that are processable and enqueues to
  // the appropriate queue based on its kind and fetch_status.
  //
  // message/reply + download  -> messageDownloadQueue
  // message/reply + decrypt    -> messageDecryptQueue
  // file          + download  -> fileDownloadQueue
  // file          + decrypt   -> fileDecryptQueue
  queueFetchesInner() {
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
        if (!item || item.fetch_status === null) {
          continue;
        }

        const isFile = item.data.kind === "file";
        const inDownloadPhase = DOWNLOAD_STATUSES.has(item.fetch_status);
        const inDecryptPhase = DECRYPT_STATUSES.has(item.fetch_status);

        if (!inDownloadPhase && !inDecryptPhase) {
          console.debug(
            "Item has unknown fetch status: ",
            item.uuid,
            item.fetch_status,
          );
          continue;
        }

        // Only enqueue new download tasks when we are online
        if (inDownloadPhase && !this.authToken) {
          continue;
        }

        const queue = isFile
          ? inDownloadPhase
            ? this.fileDownloadQueue
            : this.fileDecryptQueue
          : inDownloadPhase
            ? this.messageDownloadQueue
            : this.messageDecryptQueue;

        queue.push(task, (err, _result) => {
          if (err) {
            console.error(`Error executing fetch task in queue: `, task, err);
            try {
              if (inDownloadPhase) {
                this.db.failDownload(task.id);
              } else {
                this.db.failDecryption(task.id);
              }
            } catch (failError) {
              console.error(
                `Error failing task in queue callback for item ${task.id}:`,
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

  // Process the download: fetch item data from the server and write the ciphertext
  // to disk for decryption.
  // Then, transition the item to DecryptionInProgress so the decrypt queue
  // picks it up on the next refill.
  processDownload = async (item: ItemFetchTask, db: DB) => {
    try {
      if (!this.authToken) {
        console.debug("Not authenticated to server, skipping...");
        return;
      }
      const authToken = this.authToken;
      console.log("Processing download for item: ", item);

      const dbItem = db.getItem(item.id);
      if (
        !dbItem ||
        dbItem.fetch_status === null ||
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

      if (!DOWNLOAD_STATUSES.has(status)) {
        console.debug(
          `Item ${item.id} is not in download phase (status: ${status}), skipping...`,
        );
        return;
      }

      try {
        await this.download(item, db, metadata, progress || 0, authToken);
      } catch (e) {
        if (e instanceof DownloadCancelledError) {
          return;
        }
        throw e;
      }

      // Re-check: if the item was marked for deletion during download, stop.
      if (!this.isProcessable(item.id, db)) {
        console.debug(
          `Item ${item.id} in non-processable state after download, skipping transition to decrypt phase...`,
        );
        return;
      }

      // Transition to decrypt phase — the decrypt queue will pick this up on the next refill.
      db.setDecryptionInProgress(item.id);
    } finally {
      // After every download tick, post item state to the main thread.
      if (this.port) {
        this.port.postMessage(this.db.getItem(item.id));
      }
    }
  };

  // Process the decryption: read the ciphertext from disk, decrypt, and then
  // persist the plaintext. Clean up the on-disk ciphertext on success.
  processDecrypt = async (item: ItemFetchTask, db: DB) => {
    try {
      console.log("Processing decryption for item: ", item);

      const dbItem = db.getItem(item.id);
      if (
        !dbItem ||
        dbItem.fetch_status === null ||
        NONPROCESSABLE_FETCH_STATUSES.has(dbItem.fetch_status)
      ) {
        console.debug("Item task is not in a processable state, skipping...");
        return;
      }

      const { data: metadata, fetch_status: status } = dbItem;

      if (!DECRYPT_STATUSES.has(status)) {
        console.debug(
          `Item ${item.id} is not in decrypt phase (status: ${status}), skipping...`,
        );
        return;
      }

      try {
        await this.decrypt(item, db, metadata);
      } catch (e) {
        if (e instanceof DownloadCancelledError) {
          return;
        }
        throw e;
      }

      // After decryption, update source message preview and post to main thread.
      if (this.port) {
        this.port.postMessage(this.db.getSource(metadata.source));
      }
    } finally {
      // After every decrypt tick, post item state to the main thread.
      if (this.port) {
        this.port.postMessage(this.db.getItem(item.id));
      }
    }
  };

  // Prepare download location and writer on fs. File downloads support incremental
  // progress, whereas messages are small enough that they are always fully re-downloaded
  // on failure/retry.
  private async prepareDownload(
    item: ItemFetchTask,
    metadata: ItemMetadata,
    progress: number,
  ): Promise<{ path: string; writer: Writable; progress: number }> {
    if (
      metadata.kind !== "message" &&
      metadata.kind !== "reply" &&
      metadata.kind !== "file"
    ) {
      throw new Error(`Unsupported item kind: ${metadata.kind}`);
    }

    const downloadFilePath = this.storage.downloadFilePath(metadata, item);
    const downloadDir = path.dirname(downloadFilePath);
    await fs.promises.mkdir(downloadDir, { recursive: true });

    let resumeProgress = 0;
    if (metadata.kind === "file" && progress > 0) {
      // For files, read resume position for incremental progress
      try {
        const stats = await fs.promises.stat(downloadFilePath);
        resumeProgress = stats.size;
      } catch (error: unknown) {
        if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
          throw error;
        }
        // If file doesn't exist, start from the beginning.
      }
    }

    const downloadWriter = fs.createWriteStream(downloadFilePath, {
      flags: resumeProgress > 0 ? "a" : "w",
    });

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
    authToken: string,
  ): Promise<void> {
    console.debug(`Starting download for ${metadata.kind} ${item.id}`);
    const abortController = new AbortController();
    this.activeDownloads.set(item.id, {
      sourceUuid: metadata.source,
      controller: abortController,
    });
    try {
      db.startDownloadInProgress(item.id);
      await this.innerDownload(
        item,
        db,
        metadata,
        progress,
        abortController,
        authToken,
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
    authToken: string,
  ): Promise<void> {
    const {
      path: downloadFilePath,
      writer: downloadWriter,
      progress,
    } = await this.prepareDownload(item, metadata, originalProgress);

    const queryPath = `/api/v1/sources/${metadata.source}/${metadata.kind == "reply" ? "replies" : "submissions"}/${item.id}/download`;
    const downloadRequest: ProxyRequest = {
      method: "GET",
      path_query: queryPath,
      headers: authHeader(authToken),
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

    // Progress callback to update database and notify renderer during download.
    // Throttled to avoid overwhelming the UI (max once per 200ms).
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
      // Unset auth token on auth error
      if (downloadResponse.status === 403) {
        this.authToken = null;
      }
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
      downloadFilePath,
    );
  }

  // Verify ETag checksum for transport integrity purposes, otherwise fail terminally.
  // All downloads write to disk, so verification always reads from the file.
  private async verifyEtag(
    item: ItemFetchTask,
    db: DB,
    metadata: ItemMetadata,
    etagRaw: string | undefined,
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
    // Stream the file to avoid loading large content entirely into memory
    const readStream = fs.createReadStream(downloadFilePath);
    for await (const chunk of readStream) {
      hash.update(chunk);
    }
    const actualHash = hash.digest("hex");

    if (actualHash !== expectedHex) {
      db.terminallyFailItem(item.id);
      throw new Error(
        `ETag checksum mismatch for ${metadata.kind} ${item.id}: expected ${expectedHex}, got ${actualHash}`,
      );
    }
  }

  private async decrypt(item: ItemFetchTask, db: DB, metadata: ItemMetadata) {
    const crypto = Crypto.getInstance();
    if (!crypto) {
      throw new Error("Crypto not initialized in fetch worker, cannot decrypt");
    }

    const abortController = new AbortController();
    this.activeDecryptions.set(item.id, {
      sourceUuid: metadata.source,
      controller: abortController,
    });

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
      await this.decryptMessage(
        item,
        db,
        crypto,
        metadata,
        abortController.signal,
      );
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

  // Decrypt a message or reply. Reads ciphertext from disk, decrypts it, and persists
  // the plaintext to the DB. Cleans up the on-disk ciphertext on success.
  private async decryptMessage(
    item: ItemFetchTask,
    db: DB,
    crypto: Crypto,
    metadata: ItemMetadata,
    signal?: AbortSignal,
  ) {
    const downloadPath = this.storage.downloadFilePath(metadata, item);

    let buffer: Buffer;
    try {
      buffer = await fs.promises.readFile(downloadPath);
    } catch (error) {
      throw new Error(`Failed to load encrypted data from disk: ${error}`);
    }

    const { plaintext, doubleEncryptedKeyFingerprint } =
      await crypto.decryptMessage(buffer, signal);

    // Re-check: if the item was deleted during decryption, drop the result
    if (!this.isProcessable(item.id, db)) {
      return;
    }

    // Store the decrypted plaintext and mark item as complete
    db.completePlaintextItem(item.id, plaintext, doubleEncryptedKeyFingerprint);

    // Clean up the ciphertext file after successful decryption
    try {
      await fs.promises.unlink(downloadPath);
    } catch (error) {
      console.warn(`Failed to clean up encrypted file: ${error}`);
    }
  }

  // Decrypt an encrypted file submission. Writes the unencrypted file path
  // to the DB on success.
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
      const { finalPath, doubleEncryptedKeyFingerprint } =
        await crypto.decryptFile(
          this.storage,
          itemDirectory,
          downloadPath,
          signal,
        );

      // Re-check: if the item was deleted during decryption, drop the result
      if (!this.isProcessable(item.id, db)) {
        try {
          await fs.promises.unlink(finalPath);
        } catch (error) {
          console.warn(
            `Failed to clean up decrypted file after deletion: ${error}`,
          );
        }
        return;
      }

      // Get the decrypted file size to display to the user
      const fileStats = await fs.promises.stat(finalPath);
      const decryptedSize = fileStats.size;
      db.completeFileItem(
        item.id,
        finalPath,
        decryptedSize,
        doubleEncryptedKeyFingerprint,
      );
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
      // Merge handles tasks scheduled with the same ID.
      // We want to simply allow the existing task to keep running
      // and treat the operation as idempotent.
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
