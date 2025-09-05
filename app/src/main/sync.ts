import { proxy } from "./proxy";
import {
  ProxyJSONResponse,
  Index,
  MetadataRequest,
  MetadataResponse,
  ItemMetadata,
  SubmissionMetadata,
  ReplyMetadata,
} from "../types";
import { DB } from "./database";
import { Crypto, CryptoError } from "./crypto";
import fs from "fs";
import path from "path";
import os from "os";

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

/**
 * Download encrypted content for a submission (message or file)
 * /api/v1/sources/{source_uuid}/submissions/{submission_uuid}/download
 */
async function downloadSubmission(
  authToken: string,
  sourceUuid: string,
  submissionUuid: string,
): Promise<string> {
  // Create a temporary file to store the downloaded encrypted content
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "securedrop-"));
  const encryptedFilePath = path.join(tempDir, `${submissionUuid}.gpg`);

  try {
    // Download encrypted content using the proxy with streaming
    await proxy(
      {
        method: "GET",
        path_query: `/api/v1/sources/${sourceUuid}/submissions/${submissionUuid}/download`,
        stream: true,
        headers: {
          Authorization: `Token ${authToken}`,
        },
      },
      encryptedFilePath,
    );

    // Verify the download was successful (proxy writes to file)
    if (!fs.existsSync(encryptedFilePath)) {
      throw new Error(
        `Downloaded file not found at ${encryptedFilePath} for submission ${submissionUuid}`,
      );
    }

    return encryptedFilePath;
  } catch (error) {
    // Clean up temp directory on error
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true, force: true });
    }
    throw error;
  }
}

/**
 * Download encrypted content for a reply
 * /api/v1/sources/{source_uuid}/replies/{reply_uuid}/download
 */
async function downloadReply(
  authToken: string,
  sourceUuid: string,
  replyUuid: string,
): Promise<string> {
  // Create a temporary file to store the downloaded encrypted content
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "securedrop-"));
  const encryptedFilePath = path.join(tempDir, `${replyUuid}.gpg`);

  try {
    // Download encrypted reply content using the proxy with streaming
    await proxy(
      {
        method: "GET",
        path_query: `/api/v1/sources/${sourceUuid}/replies/${replyUuid}/download`,
        stream: true,
        headers: {
          Authorization: `Token ${authToken}`,
        },
      },
      encryptedFilePath,
    );

    // Verify the download was successful (proxy writes to file)
    if (!fs.existsSync(encryptedFilePath)) {
      throw new Error(
        `Downloaded file not found at ${encryptedFilePath} for reply ${replyUuid}`,
      );
    }

    return encryptedFilePath;
  } catch (error) {
    // Clean up temp directory on error
    if (fs.existsSync(tempDir)) {
      fs.rmSync(tempDir, { recursive: true, force: true });
    }
    throw error;
  }
}

export enum SyncStatus {
  NOT_MODIFIED = "not_modified",
  UPDATED = "updated",
  ERROR = "error",
}

/**
 * Download and decrypt messages and replies that need decryption after metadata sync
 * Processes both message submissions from sources and replies from journalists
 */
async function decryptItems(
  db: DB,
  authToken: string,
  itemsToUpdate: string[],
): Promise<void> {
  const crypto = Crypto.getInstance();
  for (const itemId of itemsToUpdate) {
    let tempFilePath: string | null = null;

    try {
      // Get the item from database to check if it needs decryption
      const items = db.getItems([itemId]);
      if (items.length === 0) {
        continue;
      }

      const item = items[0];
      const metadata = item.data as ItemMetadata;

      // Skip files (only process messages and replies)
      if (metadata.kind === "file") {
        continue;
      }

      // Skip items that are already decrypted
      if (item.plaintext) {
        continue;
      }

      if (metadata.kind === "message") {
        const submissionMetadata = metadata as SubmissionMetadata;
        console.log(`Downloading and decrypting message ${itemId}...`);

        // Download encrypted content from the API
        tempFilePath = await downloadSubmission(
          authToken,
          submissionMetadata.source,
          submissionMetadata.uuid,
        );

        // Read the encrypted file content for decryption
        const encryptedBuffer = fs.readFileSync(tempFilePath);

        // Decrypt the message content
        const decryptedMessage = await crypto.decryptMessage(encryptedBuffer);

        // Store the decrypted plaintext in the database
        db.updateItem(itemId, { plaintext: decryptedMessage });

        console.log(`Successfully decrypted message ${itemId}`);
      } else if (metadata.kind === "reply") {
        const replyMetadata = metadata as ReplyMetadata;
        console.log(`Downloading and decrypting reply ${itemId}...`);

        // Download encrypted reply content from the API
        tempFilePath = await downloadReply(
          authToken,
          replyMetadata.source,
          replyMetadata.uuid,
        );

        // Read the encrypted file content for decryption
        const encryptedBuffer = fs.readFileSync(tempFilePath);

        // Decrypt the reply content
        const decryptedReply = await crypto.decryptMessage(encryptedBuffer);

        // Store the decrypted plaintext in the database
        db.updateItem(itemId, { plaintext: decryptedReply });

        console.log(`Successfully decrypted reply ${itemId}`);
      }
    } catch (error) {
      if (error instanceof CryptoError) {
        console.error(`Failed to decrypt item ${itemId}: ${error.message}`);
        // Continue with other items rather than failing the entire sync
      } else {
        console.error(`Failed to process item ${itemId}:`, error);
        // Continue with other items rather than failing the entire sync
      }
    } finally {
      // Clean up temporary file and directory
      if (tempFilePath && fs.existsSync(tempFilePath)) {
        const tempDir = path.dirname(tempFilePath);
        fs.rmSync(tempDir, { recursive: true, force: true });
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

  // Always attempt to decrypt undecrypted messages and replies
  // This ensures that previously failed decryptions are retried on each sync
  try {
    const undecryptedMessageIds = db.getUndecryptedMessageIds();
    if (undecryptedMessageIds.length > 0) {
      console.log(
        `Found ${undecryptedMessageIds.length} undecrypted messages and replies, attempting decryption...`,
      );
      await decryptItems(db, authToken, undecryptedMessageIds);
    }
  } catch (error) {
    console.error("Error during item decryption:", error);
    // Don't fail the sync if decryption fails
  }

  return syncStatus;
}
