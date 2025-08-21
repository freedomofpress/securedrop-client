import { parentPort } from "worker_threads";

import { DB } from "../database";
import { createQueue, queueFetches } from "./queue";

console.log("Starting fetch worker...");

if (!parentPort) {
  throw new Error("Must run as a worker thread");
}

const port = parentPort;

const db = new DB();
const q = createQueue(db);

// eslint-disable-next-line @typescript-eslint/no-empty-object-type
port.on("message", (_: {}) => {
  console.log("Queueing items to be fetched");
  queueFetches(db, q);
});
