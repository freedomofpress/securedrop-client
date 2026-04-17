import { parentPort, workerData } from "worker_threads";

import { TaskQueue } from "./queue";
import { AuthedRequest } from "../../types";
import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import { Storage } from "../storage";

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

const db = new Datastore(crypto, new Storage());
const q = new TaskQueue(db, port);

type CancelMessage = {
  type: "cancel";
  itemId: string;
};

port.on("message", (message: AuthedRequest | CancelMessage) => {
  if ("type" in message && message.type === "cancel") {
    q.cancelDownload(message.itemId);
  } else {
    q.queueFetches(message as AuthedRequest);
  }
});
