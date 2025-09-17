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
      const itemsToDownload = this.db.getItemsToDownload();
      console.log("Items to download: ", itemsToDownload);
      for (const itemUUID of itemsToDownload) {
        const task: ItemFetchTask = {
          id: itemUUID,
        };
        this.queue.push(task, (err, _result) => {
          if (err) {
            console.log("Error executing fetch download task: ", task, err);
            this.db.failItem(task.id);
          }
        });
      }
    } catch (e) {
      console.log("Error queueing fetches: ", e);
    }
  }

  fetchDownload = async (item: ItemFetchTask, db: DB) => {
    console.log("Fetching downloads for: ", item);

    const [metadata, status, progress] = db.getItemWithFetchStatus(item.id);
    if (
      status == FetchStatus.Complete ||
      status == FetchStatus.FailedTerminal ||
      status == FetchStatus.Paused
    ) {
      console.log("Item task is not in an in-progress state, skipping...");
      return;
    }

    let downloadFilePath: string = "";
    let downloadWriter: Writable = new BufferedWriter();
    if (metadata.kind == "file") {
      downloadFilePath = path.join(
        os.tmpdir(),
        "download",
        metadata.source,
        item.id,
        "encrypted.gpg",
      );
      const downloadDir = path.dirname(downloadFilePath);
      await fs.promises.mkdir(downloadDir, { recursive: true });
      downloadWriter = fs.createWriteStream(downloadFilePath);
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
      throw new Error(
        `Received error from server with status ${downloadResponse.status}: ${downloadResponse.data?.toString()}`,
      );
    }

    downloadResponse = downloadResponse as ProxyStreamResponse;

    if (!downloadResponse.complete) {
      const bytesWritten = progress + downloadResponse.bytesWritten;
      db.updateInProgressItem(item.id, bytesWritten);

      throw new Error(
        `Unable to complete stream download, wrote ${downloadResponse.bytesWritten} bytes: ${downloadResponse.error?.message}`,
      );
    }

    switch (metadata.kind) {
      case "message":
      case "reply": {
        // Get the encrypted binary data from the buffer
        const bufferResult = (downloadWriter as BufferedWriter).getBuffer();

        if (bufferResult instanceof Error) {
          throw new Error(
            `Failed to get buffer from stream: ${bufferResult.message}`,
          );
        }

        try {
          // Decrypt the message/reply content
          const crypto = Crypto.getInstance();
          const decryptedContent = await crypto.decryptMessage(bufferResult);

          // Store the decrypted plaintext
          db.completePlaintextItem(item.id, decryptedContent);
          console.log(
            `Successfully decrypted ${metadata.kind} ${item.id} via fetch queue`,
          );
        } catch (error) {
          if (error instanceof CryptoError) {
            console.error(
              `Failed to decrypt ${metadata.kind} ${item.id}: ${error.message}`,
            );
            // Throw error to let the queue's retry mechanism handle it
            throw new Error(`Decryption failed: ${error.message}`);
          } else {
            throw error;
          }
        }
        break;
      }
      case "file":
        db.completeFileItem(item.id, downloadFilePath);
        break;
    }
  };
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
