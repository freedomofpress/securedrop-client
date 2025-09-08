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
        this.queue.push(task);
      }
    } catch (e) {
      console.log("Error queueing fetches: ", e);
    }
  }

  async fetchDownload(item: ItemFetchTask) {
    console.log("Fetching downloads for: ", item);

    const [metadata, status, progress] = this.db.getItemWithFetchStatus(
      item.id,
    );
    if (
      status == FetchStatus.Complete ||
      status == FetchStatus.Failed ||
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
      headers: authHeader(this?.authToken),
    };
    const downloadResponse = (await proxyStreamRequest(
      downloadRequest,
      downloadWriter,
      progress,
    )) as ProxyStreamResponse;

    // TODO: decrypt response
    if (!downloadResponse.complete) {
      const bytesWritten = progress + downloadResponse.bytesWritten;
      this.db.updateInProgressItem(item.id, bytesWritten);
      throw new Error(
        `Unable to complete stream download, total bytes written: ${bytesWritten}, chunk bytes written: ${downloadResponse.bytesWritten}`,
      );
    }

    switch (metadata.kind) {
      case "message":
      case "reply":
        this.db.completePlaintextItem(
          item.id,
          (downloadWriter as BufferedWriter).getBuffer().toString(),
        );
        break;
      case "file":
        this.db.completeFileItem(item.id, downloadFilePath);
        break;
    }
  }
}

function createQueue(
  db: DB,
  taskFn: (task: ItemFetchTask, db: DB) => void,
): Queue {
  const q: Queue = new Queue(
    function (task: ItemFetchTask, onComplete) {
      try {
        taskFn(task, db);
        onComplete();
      } catch (e) {
        console.log("Error executing fetch download task: ", task, e);
        db.failItem(task.id);
        throw e;
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
