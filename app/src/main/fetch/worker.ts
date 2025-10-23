import { parentPort, workerData } from "worker_threads";

import { DB } from "../database";
import { TaskQueue } from "./queue";
import { AuthedRequest } from "../../types";
import { Crypto } from "../crypto";

console.log("Starting fetch worker...");

if (!parentPort) {
  throw new Error("Must run as a worker thread");
}

const port = parentPort;

// Initialize crypto with workerData config if it exists and we haven't initialized yet
if (workerData?.cryptoConfig) {
  console.log("Initializing crypto with config:", workerData.cryptoConfig);
  Crypto.initialize(workerData.cryptoConfig);
}

const db = new DB();
const q = new TaskQueue(db, port);

port.on("message", (message: AuthedRequest) => {
  q.queueFetches(message);
});
