import fs from "fs";
import os from "os";
import path from "path";
import {
  afterEach,
  beforeAll,
  beforeEach,
  describe,
  expect,
  it,
  vi,
} from "vitest";

import {
  Index,
  ItemMetadata,
  ProxyJSONResponse,
  SourceMetadata,
} from "../../types";
import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import * as proxyModule from "../proxy";
import { Storage } from "../storage";
import { syncMetadata } from ".";

const SOURCE_UUID = "550e8400-e29b-41d4-a716-446655440001";
const ITEM_UUID_A = "660e8400-e29b-41d4-a716-446655440001";
const ITEM_UUID_B = "660e8400-e29b-41d4-a716-446655440002";

function sourceMetadata(): SourceMetadata {
  return {
    uuid: SOURCE_UUID,
    journalist_designation: "test journalist",
    is_starred: false,
    is_seen: false,
    has_attachment: true,
    last_updated: "2026-07-10T00:00:00Z",
    public_key: "test-public-key",
    fingerprint: "test-fingerprint",
  };
}

function itemMetadata(uuid: string, interactionCount: number): ItemMetadata {
  return {
    kind: "file",
    uuid,
    source: SOURCE_UUID,
    size: 1234,
    is_read: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

describe("item UUID sync invariant", () => {
  let crypto: Crypto;
  let db: Datastore;
  let dbDir: string;

  beforeAll(() => {
    (Crypto as any).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  });

  beforeEach(() => {
    dbDir = fs.mkdtempSync(path.join(os.tmpdir(), "sdc-item-uuid-sync-"));
    db = new Datastore(crypto, new Storage(), dbDir);
  });

  afterEach(() => {
    db.close();
    fs.rmSync(dbDir, { recursive: true, force: true });
    vi.restoreAllMocks();
  });

  it("rejects a mismatched server item before it reaches the database", async () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({ [ITEM_UUID_A]: itemMetadata(ITEM_UUID_A, 1) });

    const serverIndex: Index = db.getIndex();
    serverIndex.items[ITEM_UUID_B] = "new-item-version";
    const batchResponse = {
      sources: {},
      items: { [ITEM_UUID_B]: itemMetadata(ITEM_UUID_A, 2) },
      journalists: {},
      events: {},
    };
    const proxyMock = vi.spyOn(proxyModule, "proxyJSONRequest");
    proxyMock
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      } satisfies ProxyJSONResponse)
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: batchResponse,
        headers: new Map(),
      } satisfies ProxyJSONResponse);

    await expect(syncMetadata(db, "auth-token")).rejects.toThrow(
      "Item metadata UUID must match its batch map key",
    );

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.getItem(ITEM_UUID_B)).toBeNull();
    expect(db.getItem(ITEM_UUID_A)?.data.uuid).toBe(ITEM_UUID_A);
  });
});
