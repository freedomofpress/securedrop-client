import { parentPort, workerData } from "worker_threads";

import { DB } from "../database";
import { TaskQueue } from "./queue";
import { FetchDownloadsMessage } from "../../types";
import { Crypto } from "../crypto";

console.log("Starting fetch worker...");

if (!parentPort) {
  throw new Error("Must run as a worker thread");
}

const port = parentPort;

const db = new DB();
const q = new TaskQueue(db);

// Initialize crypto with workerData config if it exists and we haven't initialized yet
if (workerData?.cryptoConfig && !Crypto.isInitialized()) {
  console.log("Initializing crypto with config:", workerData.cryptoConfig);
  Crypto.initialize(workerData.cryptoConfig);
}

port.on("message", (message: FetchDownloadsMessage) => {
  console.log("Queueing items to be fetched");
  q.queueFetches(message);
});
