import { parentPort } from "worker_threads";

import { DB } from "../database";
import { TaskQueue } from "./queue";
import { FetchDownloadsMessage } from "../../types";

console.log("Starting fetch worker...");

if (!parentPort) {
  throw new Error("Must run as a worker thread");
}

const port = parentPort;

const db = new DB();
const q = new TaskQueue(db);

port.on("message", (message: FetchDownloadsMessage) => {
  console.log("Queueing items to be fetched");
  q.queueFetches(message);
});
