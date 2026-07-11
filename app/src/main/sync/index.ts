import { proxyJSONRequest } from "../proxy";
import {
  ProxyJSONResponse,
  Index,
  BatchRequest,
  BatchResponse,
  SyncStatus,
  IndexDeletionPlan,
  PendingEvent,
} from "../../types";
import { DB, DEFAULT_PENDING_EVENTS_LIMIT } from "../database";
import { Datastore } from "../datastore";
import {
  API_MINOR_VERSION,
  IndexSchema,
  IndexSized,
  BatchResponseSchema,
  BatchResponseSized,
  BatchRequestSchema,
  sanitizeBatchRequest,
  sanitizeBatchResponse,
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
  // require server compute time even if low payload size
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

export function reconcileIndex(
  serverIndex: Index,
  clientIndex: Index,
): { request: BatchRequest; deletions: IndexDeletionPlan } {
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
  const serverSourceSet = new Set(Object.keys(serverIndex.sources));
  const sourcesToDelete = Object.keys(clientIndex.sources).filter(
    (source) => !serverSourceSet.has(source),
  );
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
  const serverItemSet = new Set(Object.keys(serverIndex.items));
  const itemsToDelete = Object.keys(clientIndex.items).filter(
    (item) => !serverItemSet.has(item),
  );
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
  return {
    request: {
      sources: sourcesToUpdate,
      items: itemsToUpdate,
      journalists: journalistsToUpdate,
      events: [],
    },
    deletions: {
      sources: sourcesToDelete,
      items: itemsToDelete,
      journalists: journalistsToDelete,
    },
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

function getPendingEventsForAttempt(
  db: Datastore,
  attempt?: number,
): PendingEvent[] {
  if (attempt === undefined || attempt <= 0) {
    return db.getPendingEvents();
  }
  const limit = Math.max(
    1,
    Math.ceil(DEFAULT_PENDING_EVENTS_LIMIT / (attempt + 1)),
  );
  return db.getPendingEvents(limit);
}

function buildBatchPlan(
  db: Datastore,
  indexResponse: IndexResponse,
  pendingEvents: PendingEvent[],
): { request: BatchRequest; deletions: IndexDeletionPlan } {
  const emptyDeletions = { sources: [], items: [], journalists: [] };
  if (indexResponse.status !== 200) {
    return {
      request: {
        sources: [],
        items: [],
        journalists: [],
        events: pendingEvents,
      },
      deletions: emptyDeletions,
    };
  }

  const reconciliation = reconcileIndex(indexResponse.index, db.getIndex());
  reconciliation.request.events = pendingEvents;
  return reconciliation;
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
  attempt?: number,
): Promise<SyncStatus> {
  console.log("[sync] syncing ", { hintedRecords, attempt });
  await db.runFilesystemCleanupJobs();

  const currentVersion = db.getVersion();

  const pendingEvents = getPendingEventsForAttempt(db, attempt);

  const indexResponse = await getServerIndex(
    authToken,
    currentVersion,
    hintedRecords,
  );

  // Check for 403 Forbidden
  if (indexResponse.status === 403) {
    console.log("[sync] index response 403");
    return SyncStatus.FORBIDDEN;
  }

  let syncStatus = SyncStatus.NOT_MODIFIED;

  const { request, deletions } = buildBatchPlan(
    db,
    indexResponse,
    pendingEvents,
  );

  // No pending events and no server updates, nothing to sync
  if (
    indexResponse.status === 304 &&
    (!pendingEvents || pendingEvents.length == 0)
  ) {
    console.log("[sync] index up to date");
    return syncStatus;
  }

  console.log(
    "[sync] batch request:",
    JSON.stringify(sanitizeBatchRequest(request)),
  );
  const batchResponse = await submitBatch(authToken, request);
  console.log(
    "[sync] batch response:",
    JSON.stringify(
      batchResponse.status === 200
        ? { status: 200, data: sanitizeBatchResponse(batchResponse.data) }
        : batchResponse,
    ),
  );

  // Check for 403 Forbidden
  if (batchResponse.status === 403) {
    console.log("[sync] batch response 403");
    return SyncStatus.FORBIDDEN;
  }

  db.updateBatch(batchResponse.data, deletions);
  await db.runFilesystemCleanupJobs();

  syncStatus = SyncStatus.UPDATED;
  console.log("[sync] updates complete");
  return syncStatus;
}
