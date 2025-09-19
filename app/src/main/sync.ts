import { proxyJSONRequest } from "./proxy";
import {
  ProxyJSONResponse,
  Index,
  MetadataRequest,
  MetadataResponse,
  ItemMetadata,
} from "../types";
import { DB } from "./database";

async function getIndex(
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
    return resp.data as Index;
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

async function fetchMetadata(
  authToken: string,
  request: MetadataRequest,
): Promise<MetadataResponse> {
  const resp = (await proxyJSONRequest({
    method: "POST",
    path_query: "/api/v2/metadata",
    headers: {
      Accept: "application/json",
      "Content-Type": "application/json",
      Authorization: `Token ${authToken}`,
    },
    body: JSON.stringify(request),
  })) as ProxyJSONResponse;

  if (resp.error) {
    return Promise.reject(
      `Error fetching metadata from server: ${resp.status}: ${JSON.stringify(resp.data)}`,
    );
  }

  if (resp.data) {
    return resp.data as MetadataResponse;
  }
  return Promise.reject(
    `Error fetching metadata from server: ${resp.status}: no data`,
  );
}

// Given the server index and the client's index, return the sources and items
// that need to be synced. Also deletes items that are not in the server index.
export function reconcileIndex(
  db: DB,
  serverIndex: Index,
  clientIndex: Index,
): MetadataRequest {
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
    // Also check for journalists to delete
    const journalistsToDelete = Object.keys(clientIndex.journalists).filter(
      (journalist) =>
        !Object.keys(serverIndex.journalists).includes(journalist),
    );
    if (journalistsToDelete.length > 0) {
      db.deleteJournalists(journalistsToDelete);
    }
  });

  return {
    sources: sourcesToUpdate,
    items: itemsToUpdate,
    journalists: journalistsToUpdate,
  };
}

export enum SyncStatus {
  NOT_MODIFIED = "not_modified",
  UPDATED = "updated",
  ERROR = "error",
}

/**
 * Queue items for download and decryption via the fetch queue
 */
function queueItemsForDecryption(db: DB, itemsToUpdate: string[]): void {
  // Filter items that need decryption (messages and replies without plaintext)
  const itemsNeedingDecryption = itemsToUpdate.filter((itemId) => {
    const items = db.getItems([itemId]);
    if (items.length === 0) {
      return false;
    }

    const item = items[0];
    const metadata = item.data as ItemMetadata;

    // Only queue messages and replies that don't already have plaintext
    return (
      (metadata.kind === "message" || metadata.kind === "reply") &&
      !item.plaintext
    );
  });

  if (itemsNeedingDecryption.length > 0) {
    console.log(
      `Queueing ${itemsNeedingDecryption.length} items for download and decryption via fetch queue`,
    );

    // Queue each item for download by resetting their fetch status
    // The fetch queue will handle download + decryption automatically
    itemsNeedingDecryption.forEach((itemId) => {
      // Reset fetch status to Initial so the fetch queue will pick it up
      db.resetItemFetchStatus(itemId);
    });
  }
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

  let syncStatus = SyncStatus.NOT_MODIFIED;

  // Only update metadata if there are changes from the server
  if (index) {
    // Reconcile with client's index
    const clientIndex = db.getIndex();
    const metadataToUpdate = reconcileIndex(db, index, clientIndex);

    const metadata = await fetchMetadata(authToken, metadataToUpdate);
    db.updateMetadata(metadata);
    syncStatus = SyncStatus.UPDATED;
  }

  // Queue undecrypted messages and replies for download and decryption
  // This ensures that previously failed decryptions are retried via the fetch queue
  try {
    const undecryptedMessageIds = db.getUndecryptedMessageIds();
    if (undecryptedMessageIds.length > 0) {
      console.log(
        `Found ${undecryptedMessageIds.length} undecrypted messages and replies, queueing for download...`,
      );
      queueItemsForDecryption(db, undecryptedMessageIds);
    }
  } catch (error) {
    console.error("Error during item queueing:", error);
    // Don't fail the sync if queueing fails
  }

  return syncStatus;
}
