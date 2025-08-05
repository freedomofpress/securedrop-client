import { proxy } from "./proxy";
import {
  ProxyJSONResponse,
  Index,
  SourceDelta,
  SourceDeltaResponse,
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
      `Error fetching index from server: ${resp.status}: no data`,
    );
  }
}

async function syncSources(
  authToken: string,
  request: SourceDelta,
): Promise<SourceDeltaResponse> {
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
  })) as ProxyJSONResponse<SourceDeltaResponse>;

  if (resp.error) {
    return Promise.reject(
      `Error fetching synchronized sources from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return resp.data;
  }
  return Promise.reject(
    `Error fetching synchronized sources from server: ${resp.status}: no data`,
  );
}

// Given the server index and the client's index, return the sources that need to be
// fully and partially synced. Also optimistically deletes items that are not in the
// server index.
function reconcileIndex(
  db: DB,
  serverIndex: Index,
  clientIndex: Index,
): SourceDelta {
  const fullSources: string[] = [];
  const partialSources = {};
  Object.keys(serverIndex.sources).forEach((sourceID) => {
    if (!clientIndex.sources[sourceID]) {
      fullSources.push(sourceID);
    } else {
      if (
        serverIndex.sources[sourceID].version !=
        clientIndex.sources[sourceID].version
      ) {
        const itemsToUpdate: string[] = [];
        const source = serverIndex.sources[sourceID];
        const clientItemVersions = db.getSourceItemVersions(sourceID);
        if (!clientItemVersions) {
          // If there are no items for this source, we need to fetch all of them
          itemsToUpdate.push(...Object.keys(source.collection));
        } else {
          // Otherwise, check our versions against the server's versions
          Object.keys(source.collection).forEach((itemID) => {
            if (
              !clientItemVersions[itemID] ||
              clientItemVersions[itemID] != source.collection[itemID]
            ) {
              itemsToUpdate.push(itemID);
            }
            // Remove this item from the set of clientItemVersions to be processed
            delete clientItemVersions[itemID];
          });
          // Check for items that were deleted on the server, i.e. any clientItemVersions
          // remaining that were not processed
          const itemsToDelete = Object.keys(clientItemVersions);
          if (itemsToDelete.length != 0) {
            db.deleteItems(itemsToDelete);
          }
          if (itemsToUpdate.length != 0) {
            partialSources[sourceID] = itemsToUpdate;
          }
        }
      }
    }
    // Remove this from the set of clientIndex.sources to be processed
    delete clientIndex.sources[sourceID];
  });
  // Check for sources that were deleted on the server, i.e. any clientIndex.sources remaining
  // that were not processed.
  const sourcesToDelete = Object.keys(clientIndex.sources);
  if (sourcesToDelete.length != 0) {
    db.deleteSources(sourcesToDelete);
  }
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
  const sourceDelta = reconcileIndex(db, index, clientIndex);

  const sources = await syncSources(authToken, sourceDelta);
  db.updateSources(sources);
  return SyncStatus.UPDATED;
}
