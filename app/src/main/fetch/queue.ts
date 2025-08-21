import Queue from "better-queue";

import { DB } from "../database";
import { FetchStatus } from "../../types";

export type ItemFetchTask = {
  id: string;
};

export function createQueue(db: DB): Queue {
  const q: Queue = new Queue(
    function (task: ItemFetchTask, onComplete) {
      try {
        fetchDownload(task, db);
        onComplete();
      } catch (e) {
        console.log("Error executing fetch download task: ", task, e);
        db.failItem(task.id);
        throw e;
      }
    },
    {
      batchSize: 1,
      maxTimeout: 30_000,
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

// Queries the database for all items that need to be downloaded and queues
// up download tasks to be processed.
export async function queueFetches(db: DB, queue: Queue) {
  try {
    const itemsToDownload = db.getItemsToDownload();
    console.log("Items to download: ", itemsToDownload);
    for (const itemUUID of itemsToDownload) {
      const task: ItemFetchTask = {
        id: itemUUID,
      };
      queue.push(task);
    }
  } catch (e) {
    console.log("Error queueing fetches: ", e);
  }
}

export async function fetchDownload(item: ItemFetchTask, db: DB) {
  console.log("Fetching downloads for: ", item);

  const [status, _progress] = db.getItemFetchStatus(item.id);
  if (
    status == FetchStatus.Complete ||
    status == FetchStatus.Failed ||
    status == FetchStatus.Paused
  ) {
    console.log("Item task is not in an in-progress state, skipping...");
    return;
  }

  // TODO: perform download + decryption
  // checkpoint progress in the DB
  //
  // For now, just mark as complete with empty plaintext
  db.completePlaintextItem(item.id, "");
}
