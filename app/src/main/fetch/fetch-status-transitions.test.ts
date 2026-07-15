import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import fs from "fs";
import os from "os";
import path from "path";

import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import { Storage } from "../storage";
import {
  FetchStatus,
  ItemMetadata,
  PendingEventType,
  SourceMetadata,
} from "../../types";
import { TaskQueue } from "./queue";

const SOURCE_UUID = "11111111-1111-4111-8111-111111111111";
const UNKNOWN_FETCH_STATUS = 10;

function sourceMetadata(): SourceMetadata {
  return {
    uuid: SOURCE_UUID,
    journalist_designation: "alpha bravo",
    is_starred: false,
    is_seen: false,
    has_attachment: true,
    last_updated: "2026-01-01T00:00:00Z",
    public_key: "test public key",
    fingerprint: "test fingerprint",
  };
}

function itemMetadata(
  uuid: string,
  kind: "file" | "message",
  interactionCount: number,
): ItemMetadata {
  return {
    kind,
    uuid,
    source: SOURCE_UUID,
    size: 128,
    is_read: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

describe("fetch status transition guards", () => {
  const originalHomedir = os.homedir;
  let originalCryptoInstance: unknown;
  let testHomeDir = "";
  let db: Datastore;

  beforeEach(() => {
    testHomeDir = fs.mkdtempSync(path.join(os.tmpdir(), "sd-fetch-status-"));
    os.homedir = () => testHomeDir;
    originalCryptoInstance = (Crypto as unknown as { instance?: unknown })
      .instance;
    db = new Datastore({} as Crypto, new Storage());
  });

  afterEach(() => {
    vi.restoreAllMocks();
    db.close();
    (Crypto as unknown as { instance?: unknown }).instance =
      originalCryptoInstance;
    os.homedir = originalHomedir;
    fs.rmSync(testHomeDir, { recursive: true, force: true });
  });

  it("rejects late worker and renderer transitions after source deletion", () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });

    const transitions = [
      {
        name: "start download",
        apply: (uuid: string) => db.startDownloadInProgress(uuid),
      },
      {
        name: "download progress",
        apply: (uuid: string) => db.updateDownloadInProgress(uuid, 64),
      },
      {
        name: "start decryption",
        apply: (uuid: string) => db.setDecryptionInProgress(uuid),
      },
      {
        name: "download failure",
        apply: (uuid: string) => db.failDownload(uuid),
      },
      {
        name: "decryption failure",
        apply: (uuid: string) => db.failDecryption(uuid),
      },
      {
        name: "terminal failure",
        apply: (uuid: string) => db.terminallyFailItem(uuid),
      },
      {
        name: "pause",
        apply: (uuid: string) => db.pauseItem(uuid),
      },
      {
        name: "resume",
        apply: (uuid: string) => db.resumeItem(uuid),
      },
      {
        name: "plaintext completion",
        apply: (uuid: string) => db.completePlaintextItem(uuid, "plaintext"),
      },
      {
        name: "file completion",
        apply: (uuid: string) => db.completeFileItem(uuid, "/tmp/file", 8),
      },
      {
        name: "renderer resume",
        apply: (uuid: string) =>
          db.updateFetchStatus(uuid, FetchStatus.DownloadInProgress),
      },
    ];
    const items = Object.fromEntries(
      transitions.map(({ name }, index) => [
        `item-${index}`,
        itemMetadata(
          `item-${index}`,
          name === "file completion" ? "file" : "message",
          index + 1,
        ),
      ]),
    );
    db.updateItems(items);

    expect(
      db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted),
    ).not.toBeNull();

    transitions.forEach(({ name, apply }, index) => {
      const uuid = `item-${index}`;
      apply(uuid);
      expect(db.getItem(uuid)?.fetch_status, name).toBe(
        FetchStatus.ScheduledDeletion,
      );
    });
    expect(db.getItemsToProcess({ messageLimit: 20, fileLimit: 20 })).toEqual(
      [],
    );
  });

  it("guards truncated items without blocking later conversation items", () => {
    const truncatedUuid = "old-message";
    const retainedUuid = "new-message";
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({
      [truncatedUuid]: itemMetadata(truncatedUuid, "message", 1),
      [retainedUuid]: itemMetadata(retainedUuid, "message", 2),
    });
    db.setDecryptionInProgress(truncatedUuid);

    expect(
      db.addPendingSourceEvent(
        SOURCE_UUID,
        PendingEventType.SourceConversationTruncated,
        { upper_bound: 1 },
      ),
    ).not.toBeNull();

    db.failDecryption(truncatedUuid);
    expect(
      db.updateFetchStatus(truncatedUuid, FetchStatus.DownloadInProgress),
    ).toBe(false);
    expect(db.getItem(truncatedUuid)?.fetch_status).toBe(
      FetchStatus.ScheduledDeletion,
    );

    expect(
      db.updateFetchStatus(retainedUuid, FetchStatus.DownloadInProgress),
    ).toBe(true);
    expect(db.getItemsToProcess({ messageLimit: 20, fileLimit: 20 })).toEqual([
      retainedUuid,
    ]);
  });

  it("rejects worker-only statuses from the renderer write boundary", () => {
    const itemUuid = "renderer-item";
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({
      [itemUuid]: itemMetadata(itemUuid, "message", 1),
    });

    expect(
      db.updateFetchStatus(itemUuid, FetchStatus.DecryptionInProgress),
    ).toBe(false);
    expect(db.getItem(itemUuid)?.fetch_status).toBe(FetchStatus.Initial);
  });

  it("rejects unknown persisted statuses at worker write boundaries", () => {
    const transitions = [
      (uuid: string) => db.startDownloadInProgress(uuid),
      (uuid: string) => db.updateDownloadInProgress(uuid, 64),
      (uuid: string) => db.failDownload(uuid),
      (uuid: string) => db.failDecryption(uuid),
      (uuid: string) => db.setDecryptionInProgress(uuid),
      (uuid: string) => db.terminallyFailItem(uuid),
      (uuid: string) => db.pauseItem(uuid),
      (uuid: string) => db.resumeItem(uuid),
      (uuid: string) => db.completePlaintextItem(uuid, "plaintext"),
      (uuid: string) => db.completeFileItem(uuid, "/tmp/file", 8),
    ];
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems(
      Object.fromEntries(
        transitions.map((_, index) => [
          `unknown-worker-${index}`,
          itemMetadata(`unknown-worker-${index}`, "message", index + 1),
        ]),
      ),
    );

    transitions.forEach((transition, index) => {
      const uuid = `unknown-worker-${index}`;
      db["db"]!.prepare("UPDATE items SET fetch_status = ? WHERE uuid = ?").run(
        UNKNOWN_FETCH_STATUS,
        uuid,
      );

      expect(transition(uuid)).toBe(false);
      expect(db.getItem(uuid)?.fetch_status).toBe(UNKNOWN_FETCH_STATUS);
    });
  });

  it("rejects unknown persisted statuses at the renderer write boundary", () => {
    const itemUuid = "unknown-renderer";
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({
      [itemUuid]: itemMetadata(itemUuid, "file", 1),
    });
    db["db"]!.prepare("UPDATE items SET fetch_status = ? WHERE uuid = ?").run(
      UNKNOWN_FETCH_STATUS,
      itemUuid,
    );

    for (const status of [
      FetchStatus.DownloadInProgress,
      FetchStatus.Paused,
      FetchStatus.Cancelled,
    ]) {
      expect(db.updateFetchStatus(itemUuid, status)).toBe(false);
      expect(db.getItem(itemUuid)?.fetch_status).toBe(UNKNOWN_FETCH_STATUS);
    }
  });

  it("rejects deletion in the queue post-check completion race", async () => {
    const itemUuid = "22222222-2222-4222-8222-222222222222";
    const storage = new Storage();
    const metadata = itemMetadata(itemUuid, "file", 1);
    const decryptFile = vi.fn(
      async (
        _storage: Storage,
        itemDirectory: { join: (name: string) => string },
      ): Promise<string> => {
        const finalPath = itemDirectory.join("decrypted.txt");
        await fs.promises.writeFile(finalPath, "plaintext after deletion");
        return finalPath;
      },
    );
    const crypto = { decryptFile, decryptMessage: vi.fn() };
    (Crypto as unknown as { instance?: unknown }).instance = crypto;

    db.close();
    db = new Datastore(crypto as unknown as Crypto, storage);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({ [itemUuid]: metadata });
    db.setDecryptionInProgress(itemUuid);

    const queue = new TaskQueue(db);
    const encryptedPath = queue.storage.downloadFilePath(metadata, {
      id: itemUuid,
    });
    await fs.promises.writeFile(encryptedPath, "encrypted file bytes");

    const realStat = fs.promises.stat.bind(fs.promises);
    let finalPath = "";
    vi.spyOn(fs.promises, "stat").mockImplementation(async (target) => {
      if (String(target).endsWith("decrypted.txt")) {
        finalPath = String(target);
        db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted);
      }
      return realStat(target);
    });

    await queue.processDecrypt({ id: itemUuid }, db);

    const item = db.getItem(itemUuid);
    expect(decryptFile).toHaveBeenCalledOnce();
    expect(item?.fetch_status).toBe(FetchStatus.ScheduledDeletion);
    expect(item?.filename).toBeNull();
    expect(item?.decrypted_size).toBeNull();
    expect(fs.existsSync(finalPath)).toBe(false);
  });
});
