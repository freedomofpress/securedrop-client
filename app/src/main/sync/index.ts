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
  API_MINOR_VERSION,
  IndexSchema,
  BatchResponseSchema,
  BatchRequestSchema,
} from "../../schemas";
import { estimateTimeout } from "../timeouts";

import * as fs from "fs";
import { Storage } from "../storage";

type IndexResponse =
  | { status: 200; index: Index }
  | { status: 304 }
  | { status: 403 };

async function getServerIndex(
  authToken: string,
  currentVersion: string,
  records?: number,
): Promise<IndexResponse> {
  const timeout = estimateTimeout(IndexSchema, records);
  const resp = (await proxyJSONRequest(
    {
      method: "GET",
      path_query: "/api/v2/index",
      headers: {
        Accept: "application/json",
        "Content-Type": "application/json",
        Authorization: `Token ${authToken}`,
        "If-None-Match": currentVersion,
        Prefer: `securedrop=${API_MINOR_VERSION}`,
      },
    },
    undefined, // abortSignal
    timeout,
  )) as ProxyJSONResponse;

  if (resp.error) {
    if (resp.status === 403) {
      return { status: 403 };
    }
    return Promise.reject(
      `Error fetching index from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return { status: 200, index: IndexSchema.parse(resp.data) };
  }

  // Version matches, there's nothing to do!
  if (resp.status == 304) {
    return { status: 304 };
  } else {
    return Promise.reject(
      `Error fetching index from server: ${resp.status}: no data`,
    );
  }
}

type BatchSubmitResponse =
  | { status: 200; data: BatchResponse }
  | { status: 403 };

async function submitBatch(
  authToken: string,
  request: BatchRequest,
): Promise<BatchSubmitResponse> {
  // (sources + items) >> (journalists + events), so the former is good enough
  // for estimation.
  const records = (request.sources?.length || 0) + (request.items?.length || 0);
  const timeout = estimateTimeout(BatchResponseSchema, records);

  const resp = (await proxyJSONRequest(
    {
      method: "POST",
      path_query: "/api/v2/data",
      headers: {
        Accept: "application/json",
        "Content-Type": "application/json",
        Authorization: `Token ${authToken}`,
        Prefer: `securedrop=${API_MINOR_VERSION}`,
      },
      body: JSON.stringify(BatchRequestSchema.parse(request)),
    },
    undefined, // abortSignal
    timeout,
  )) as ProxyJSONResponse;

  if (resp.error) {
    if (resp.status === 403) {
      return { status: 403 };
    }
    return Promise.reject(
      `Error fetching data from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return { status: 200, data: BatchResponseSchema.parse(resp.data) };
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

// Returns true if the database is already at the hinted version and there are
// no pending events to flush.  This check MAY be used immediately after login
// to save a round trip.  However, since the hinted version is updated only at
// login, this check MUST NOT be used to skip any other sync, or the client will
// never update during this session!
export function shouldSkipSync(db: DB, hintedVersion?: string): boolean {
  const nothingIncoming = db.getVersion() === hintedVersion;
  const nothingOutgoing = db.getPendingEvents().length === 0;
  return nothingIncoming && nothingOutgoing;
}

// Executes metadata sync with SecureDrop server, updating
// the current version and persisting updated source, reply,
// and submission metadata to the DB.
// Note: metadata sync may eventually only update an in-memory
// fetch/download queue rather than persisting to DB.
export async function syncMetadata(
  db: DB,
  authToken: string,
  hintedRecords?: number,
): Promise<SyncStatus> {
  const currentVersion = db.getVersion();
  const pendingEvents = db.getPendingEvents();
  const indexResponse = await getServerIndex(
    authToken,
    currentVersion,
    hintedRecords,
  );

  // Check for 403 Forbidden
  if (indexResponse.status === 403) {
    return SyncStatus.FORBIDDEN;
  }

  let syncStatus = SyncStatus.NOT_MODIFIED;

  const request: BatchRequest = {
    sources: [],
    items: [],
    journalists: [],
    events: pendingEvents,
  };

  if (indexResponse.status === 200) {
    // Reconcile with client's index to get metadata to update
    const clientIndex = db.getIndex();
    const { sources, items, journalists } = reconcileIndex(
      db,
      indexResponse.index,
      clientIndex,
    );
    request.sources = sources;
    request.items = items;
    request.journalists = journalists;
  }

  // No pending events and no server updates, nothing to sync
  if (
    indexResponse.status === 304 &&
    (!pendingEvents || pendingEvents.length == 0)
  ) {
    return syncStatus;
  }

  const batchResponse = await submitBatch(authToken, request);

  // Check for 403 Forbidden
  if (batchResponse.status === 403) {
    return SyncStatus.FORBIDDEN;
  }

  db.updateBatch(batchResponse.data);
  syncStatus = SyncStatus.UPDATED;

  return syncStatus;
}
