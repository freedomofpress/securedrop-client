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
if (!workerData.cryptoConfig) {
  throw new Error("Worker missing crypto config");
}

console.log("Initializing crypto with config:", workerData.cryptoConfig);
const crypto = Crypto.initialize(workerData.cryptoConfig);

const db = new DB(crypto);
const q = new TaskQueue(db, port);

port.on("message", (message: AuthedRequest) => {
  q.queueFetches(message);
});
