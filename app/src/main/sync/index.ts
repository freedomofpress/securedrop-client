import { proxyJSONRequest } from "../proxy";
import {
  ProxyJSONResponse,
  Index,
  BatchRequest,
  BatchResponse,
  SyncStatus,
} from "../../types";
import { DB } from "../database";
import { Datastore } from "../datastore";
import {
  API_MINOR_VERSION,
  IndexSchema,
  IndexSized,
  BatchResponseSchema,
  BatchResponseSized,
  BatchRequestSchema,
} from "../../schemas";
import { estimateTimeout } from "../timeouts";

type IndexResponse =
  | { status: 200; index: Index }
  | { status: 304 }
  | { status: 403 };

async function getServerIndex(
  authToken: string,
  currentVersion: string,
  records?: number,
): Promise<IndexResponse> {
  const timeout = estimateTimeout(IndexSized, records);
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
  // we include sources, items, and also events in the timeout since events may
  // require serve compute time even if low payload size
  const records =
    (request.sources?.length || 0) +
    (request.items?.length || 0) +
    (request.events?.length || 0);
  const timeout = estimateTimeout(BatchResponseSized, records);

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
  db: Datastore,
  serverIndex: Index,
  clientIndex: Index,
): BatchRequest {
  const pendingDeletionSources = db.getSourcesScheduledForDeletion();

  const sourcesToUpdate: string[] = [];
  Object.keys(serverIndex.sources).forEach((sourceID) => {
    if (pendingDeletionSources.has(sourceID)) {
      return;
    }
    if (
      !clientIndex.sources[sourceID] ||
      serverIndex.sources[sourceID] != clientIndex.sources[sourceID]
    ) {
      sourcesToUpdate.push(sourceID);
    }
  });
  // Check for sources to delete, which are ones that the client has which
  // are no longer on the server.
  const serverSourceSet = new Set(Object.keys(serverIndex.sources));
  const sourcesToDelete = Object.keys(clientIndex.sources).filter(
    (source) => !serverSourceSet.has(source),
  );
  if (sourcesToDelete.length > 0) {
    db.deleteSources(sourcesToDelete);
  }

  const itemsToUpdate: string[] = [];
  const pendingDeletionItems = db.getItemsScheduledForDeletion();
  Object.keys(serverIndex.items).forEach((itemID) => {
    if (pendingDeletionItems.has(itemID)) {
      return;
    }
    if (
      !clientIndex.items[itemID] ||
      serverIndex.items[itemID] != clientIndex.items[itemID]
    ) {
      itemsToUpdate.push(itemID);
    }
  });
  // Also check for items to delete
  const serverItemSet = new Set(Object.keys(serverIndex.items));
  const itemsToDelete = Object.keys(clientIndex.items).filter(
    (item) => !serverItemSet.has(item),
  );
  if (itemsToDelete.length > 0) {
    db.deleteItems(itemsToDelete);
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
  const serverJournalistSet = new Set(Object.keys(serverIndex.journalists));
  const journalistsToDelete = Object.keys(clientIndex.journalists).filter(
    (journalist) => !serverJournalistSet.has(journalist),
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
  db: Datastore,
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

  console.debug("Client batch request: ", request);
  const batchResponse = await submitBatch(authToken, request);
  console.debug("Server batch response: ", batchResponse);

  // Check for 403 Forbidden
  if (batchResponse.status === 403) {
    return SyncStatus.FORBIDDEN;
  }

  db.updateBatch(batchResponse.data);

  syncStatus = SyncStatus.UPDATED;
  return syncStatus;
}
