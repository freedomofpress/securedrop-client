import { proxyJSONRequest } from "../proxy";
import {
  ProxyJSONResponse,
  Index,
  BatchRequest,
  BatchResponse,
  SyncStatus,
  type Item,
} from "../../types";
import { DB } from "../database";
import {
  IndexSchema,
  BatchResponseSchema,
  BatchRequestSchema,
} from "../../schemas";

import * as fs from "fs";
import { Storage } from "../storage";

async function getServerIndex(
  authToken: string,
  currentVersion: string,
): Promise<Index | null> {
  const resp = (await proxyJSONRequest({
    method: "GET",
    path_query: "/api/v2/index",
    headers: {
      Accept: "application/json",
      "Content-Type": "application/json",
      Authorization: `Token ${authToken}`,
      "If-None-Match": currentVersion,
    },
  })) as ProxyJSONResponse;

  if (resp.error) {
    return Promise.reject(
      `Error fetching index from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return IndexSchema.parse(resp.data);
  }

  // Version matches, there's nothing to do!
  if (resp.status == 304) {
    return null;
  } else {
    return Promise.reject(
      `Error fetching index from server: ${resp.status}: no data`,
    );
  }
}

async function submitBatch(
  authToken: string,
  request: BatchRequest,
): Promise<BatchResponse> {
  const resp = (await proxyJSONRequest({
    method: "POST",
    path_query: "/api/v2/data",
    headers: {
      Accept: "application/json",
      "Content-Type": "application/json",
      Authorization: `Token ${authToken}`,
    },
    body: JSON.stringify(BatchRequestSchema.parse(request)),
  })) as ProxyJSONResponse;

  if (resp.error) {
    return Promise.reject(
      `Error fetching data from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return BatchResponseSchema.parse(resp.data);
  }
  return Promise.reject(
    `Error fetching data from server: ${resp.status}: no data`,
  );
}

// Given the server index and the client's index, return the sources and items
// that need to be synced. Also deletes items that are not in the server index.
export function reconcileIndex(
  db: DB,
  serverIndex: Index,
  clientIndex: Index,
): BatchRequest {
  const sourcesToUpdate: string[] = [];
  Object.keys(serverIndex.sources).forEach((sourceID) => {
    if (
      !clientIndex.sources[sourceID] ||
      serverIndex.sources[sourceID] != clientIndex.sources[sourceID]
    ) {
      sourcesToUpdate.push(sourceID);
    }
  });
  // Check for sources to delete, which are ones that the client has which
  // are no longer on the server.
  const sourcesToDelete = Object.keys(clientIndex.sources).filter(
    (source) => !Object.keys(serverIndex.sources).includes(source),
  );
  if (sourcesToDelete.length > 0) {
    db.deleteSources(sourcesToDelete);
  }

  const itemsToUpdate: string[] = [];
  Object.keys(serverIndex.items).forEach((itemID) => {
    if (
      !clientIndex.items[itemID] ||
      serverIndex.items[itemID] != clientIndex.items[itemID]
    ) {
      itemsToUpdate.push(itemID);
    }
  });
  // Also check for items to delete
  const itemsToDelete = Object.keys(clientIndex.items).filter(
    (item) => !Object.keys(serverIndex.items).includes(item),
  );
  if (itemsToDelete.length > 0) {
    deleteItems(db, itemsToDelete);
  }

  const journalistsToUpdate: string[] = [];
  Object.keys(serverIndex.journalists).forEach((journalistID) => {
    if (
      !clientIndex.journalists[journalistID] ||
      serverIndex.journalists[journalistID] !=
        clientIndex.journalists[journalistID]
    ) {
      journalistsToUpdate.push(journalistID);
    }
  });
  // Also check for journalists to delete
  const journalistsToDelete = Object.keys(clientIndex.journalists).filter(
    (journalist) => !Object.keys(serverIndex.journalists).includes(journalist),
  );
  if (journalistsToDelete.length > 0) {
    db.deleteJournalists(journalistsToDelete);
  }

  return {
    sources: sourcesToUpdate,
    items: itemsToUpdate,
    journalists: journalistsToUpdate,
    events: [],
  };
}

// Delete items from DB and delete any files persisted to disk from
// the filesystem.
function deleteItems(db: DB, itemIDs: string[]) {
  const storage = new Storage();
  // Perform fs cleanup
  for (const itemID of itemIDs) {
    let item: Item | null = null;
    try {
      item = db.getItem(itemID);
    } catch (_error) {
      continue;
    }
    if (!item) {
      continue;
    }
    // Clean up the raw file
    if (item.filename) {
      fs.rmSync(item.filename, { force: true });
    }
    // and the item folder too
    const itemDirectory = storage.itemDirectory(item.data);
    if (fs.existsSync(itemDirectory.path)) {
      fs.rmSync(itemDirectory.path, { recursive: true, force: true });
    }
  }

  db.deleteItems(itemIDs);
}

// Executes metadata sync with SecureDrop server, updating
// the current version and persisting updated source, reply,
// and submission metadata to the DB.
// Note: metadata sync may eventually only update an in-memory
// fetch/download queue rather than persisting to DB.
export async function syncMetadata(
  db: DB,
  authToken: string,
): Promise<SyncStatus> {
  const currentVersion = db.getVersion();
  const pendingEvents = db.getPendingEvents();
  const serverIndex = await getServerIndex(authToken, currentVersion);

  let syncStatus = SyncStatus.NOT_MODIFIED;

  const request: BatchRequest = {
    sources: [],
    items: [],
    journalists: [],
    events: pendingEvents,
  };

  if (serverIndex) {
    // Reconcile with client's index to get metadata to update
    const clientIndex = db.getIndex();
    const { sources, items, journalists } = reconcileIndex(
      db,
      serverIndex,
      clientIndex,
    );
    request.sources = sources;
    request.items = items;
    request.journalists = journalists;
  }

  // No pending events and no server updates, nothing to sync
  if (!serverIndex && (!pendingEvents || pendingEvents.length == 0)) {
    return syncStatus;
  }

  const batchResponse = await submitBatch(authToken, request);

  db.updateBatch(batchResponse);
  syncStatus = SyncStatus.UPDATED;

  return syncStatus;
}
