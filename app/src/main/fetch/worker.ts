import { parentPort, workerData } from "worker_threads";

import { TaskQueue } from "./queue";
import { FetchWorkerMessage } from "../../types";
import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import { Storage } from "../storage";
import { initLogging } from "../log";

initLogging();

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

port.on("message", (message: FetchWorkerMessage) => {
  if (!("type" in message)) {
    console.error("Unrecognized message: ", message);
  }
  switch (message.type) {
    case "cancel":
      q.cancelDownload(message.itemId);
      break;
    case "abortSourceFetch":
      q.abortSourceFetch(message.sourceUuid);
      break;
    case "authedRequest":
      q.queueFetches(message.request);
      break;
    case "exit": {
      console.log("Received exit message, shutting down...");
      db.close();
      process.exit(0);
    }
  }
});
