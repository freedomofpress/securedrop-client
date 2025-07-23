import { proxy } from "./proxy";
import {
  ProxyJSONResponse,
  Index,
  SourceSyncRequest,
  SourceSyncResponse,
} from "../types";
import { DB } from "./database";

async function getIndex(
  authToken: string,
  currentVersion: string,
): Promise<Index | null> {
  const resp = (await proxy({
    method: "GET",
    path_query: "/api/v2/index",
    stream: false,
    headers: {
      Accept: "application/json",
      "Content-Type": "application/json",
      Authorization: `Token ${authToken}`,
      "If-None-Match": currentVersion,
    },
  })) as ProxyJSONResponse<Index>;

  if (resp.error) {
    return Promise.reject(
      `Error fetching index from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return resp.data;
  }

  // Version matches, there's nothing to do!
  if (resp.status == 304) {
    return null;
  } else {
    return Promise.reject(
      `Error fetching index from server: bad status code ${resp.status}`,
    );
  }
}

async function syncSources(
  authToken: string,
  request: SourceSyncRequest,
): Promise<SourceSyncResponse> {
  const resp = (await proxy({
    method: "POST",
    path_query: "/api/v2/sources",
    stream: false,
    headers: {
      Accept: "application/json",
      "Content-Type": "application/json",
      Authorization: `Token ${authToken}`,
    },
    body: JSON.stringify(request),
  })) as ProxyJSONResponse<SourceSyncResponse>;

  if (resp.error || resp.status != 200) {
    return Promise.reject(
      `Error fetching synchronized sources from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return resp.data;
  }
  return Promise.reject(
    `Error fetching synchronized sources from server: no data returned`,
  );
}

function reconcileIndex(
  db: DB,
  serverIndex: Index,
  clientIndex: Index,
): SourceSyncRequest {
  const fullSources: string[] = [];
  const partialSources = {};
  Object.keys(serverIndex.sources).forEach((uuid) => {
    if (!clientIndex.sources[uuid]) {
      fullSources.push(uuid);
    } else {
      if (
        serverIndex.sources[uuid].version != clientIndex.sources[uuid].version
      ) {
        const itemsToUpdate: string[] = [];
        const source = serverIndex.sources[uuid];
        const clientItemVersions = db.getSourceItemVersions(uuid);
        Object.keys(source.collection).forEach((itemID) => {
          if (
            !clientItemVersions ||
            !clientItemVersions[itemID] ||
            clientItemVersions[itemID] != source.collection[itemID]
          ) {
            itemsToUpdate.push(itemID);
          }
        });
        partialSources[uuid] = itemsToUpdate;
      }
    }
  });
  return {
    full_sources: fullSources,
    partial_sources: partialSources,
  };
}

export enum SyncStatus {
  NOT_MODIFIED = "not_modified",
  UPDATED = "updated",
  ERROR = "error",
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
  const index = await getIndex(authToken, currentVersion);
  // Versions match, sync is complete
  if (!index) {
    return SyncStatus.NOT_MODIFIED;
  }

  // Reconcile with client's index
  const clientIndex = db.getIndex();
  const sourceSyncRequest = reconcileIndex(db, index, clientIndex);

  const sources = await syncSources(authToken, sourceSyncRequest);
  db.updateSources(sources);
  return SyncStatus.UPDATED;
}
