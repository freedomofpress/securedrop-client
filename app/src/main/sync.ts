import { proxy } from "./proxy";
import {
  ProxyJSONResponse,
  Index,
  MetadataRequest,
  MetadataResponse,
  ItemMetadata,
  SubmissionMetadata,
} from "../types";
import { DB } from "./database";
import { CryptoError } from "./crypto";

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
  const resp = (await proxy({
    method: "POST",
    path_query: "/api/v2/metadata",
    stream: false,
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
 * Decrypt messages that need decryption after metadata sync
 */
async function decryptItems(db: DB, itemsToUpdate: string[]): Promise<void> {
  for (const itemId of itemsToUpdate) {
    try {
      // Get the item from database to check if it needs decryption
      const items = db.getItems([itemId]);
      if (items.length === 0) {
        continue;
      }

      const item = items[0];
      const metadata = item.data as ItemMetadata;

      // Skip replies and files
      if (metadata.kind === "reply" || metadata.kind == "file") {
        continue;
      }

      // Skip message items that are already decrypted
      if (item.plaintext) {
        continue;
      }

      const submissionMetadata = metadata as SubmissionMetadata;

      if (submissionMetadata.kind === "message") {
        // TODO: Download and decrypt message
        // const decryptedMessage = await downloadAndDecryptMessage(itemId, authToken);
        // db.updateItem(itemId, { plaintext: decryptedMessage });
      }
    } catch (error) {
      if (error instanceof CryptoError) {
        console.error(`Failed to decrypt item ${itemId}: ${error.message}`);
        // Continue with other items rather than failing the entire sync
      } else {
        throw error;
      }
    }
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
  // Versions match, sync is complete
  if (!index) {
    return SyncStatus.NOT_MODIFIED;
  }

  // Reconcile with client's index
  const clientIndex = db.getIndex();
  const metadataToUpdate = reconcileIndex(db, index, clientIndex);

  const metadata = await fetchMetadata(authToken, metadataToUpdate);
  db.updateMetadata(metadata);

  // Decrypt newly updated items
  if (metadataToUpdate.items.length > 0) {
    try {
      await decryptItems(db, metadataToUpdate.items);
    } catch (error) {
      console.error("Error during item decryption:", error);
      // Don't fail the sync if decryption fails
    }
  }

  return SyncStatus.UPDATED;
}
