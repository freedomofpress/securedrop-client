import { describe, it, expect, vi, beforeEach, MockInstance } from "vitest";
import * as syncModule from "../../../src/main/sync";
import { DB } from "../../../src/main/database";
import {
  Index,
  ProxyJSONResponse,
  MetadataResponse,
  SourceMetadata,
  ItemMetadata,
  JournalistMetadata,
  SyncStatus,
} from "../../../src/types";
import * as proxyModule from "../../../src/main/proxy";
import { encryptedFilepath } from "../crypto";
import fs from "fs";

vi.mock("fs", () => ({
  default: {
    rmSync: vi.fn(),
  },
}));

// Valid UUIDs for testing
const SOURCE_UUID_1 = "550e8400-e29b-41d4-a716-446655440001";
const SOURCE_UUID_2 = "550e8400-e29b-41d4-a716-446655440002";
const ITEM_UUID_1 = "660e8400-e29b-41d4-a716-446655440001";
const ITEM_UUID_2 = "660e8400-e29b-41d4-a716-446655440002";
const JOURNALIST_UUID_1 = "770e8400-e29b-41d4-a716-446655440001";

function mockDB({
  index = { sources: {}, items: {}, journalists: {} },
  itemFileData = {},
} = {}) {
  return {
    getVersion: vi.fn(() => "v1"),
    getIndex: vi.fn(() => index),
    deleteItems: vi.fn((_itemIDs) => {}),
    deleteSources: vi.fn((_sourceIDs) => {}),
    updateMetadata: vi.fn((_metadata) => {}),
    getItemFileData: vi.fn(() => itemFileData),
  } as unknown as DB;
}

function mockSourceMetadata(uuid: string): SourceMetadata {
  return {
    uuid: uuid,
    journalist_designation: "test journalist",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    last_updated: new Date().toISOString(),
    public_key: "test_public_key",
    fingerprint: "test_fingerprint",
  };
}

function mockItemMetadata(uuid: string, source_uuid: string): ItemMetadata {
  return {
    kind: "reply",
    uuid: uuid,
    source: source_uuid,
    size: 1234,
    journalist_uuid: JOURNALIST_UUID_1,
    is_deleted_by_source: false,
    seen_by: [],
    interaction_count: 1,
  };
}

function mockJournalistMetadata(uuid: string): JournalistMetadata {
  return {
    uuid: uuid,
    username: "test_journalist",
    first_name: "foo",
    last_name: "bar",
  };
}

describe("syncMetadata", () => {
  let db: DB;

  function mockProxyResponses(responses: ProxyJSONResponse[]): MockInstance {
    const mock = vi.spyOn(proxyModule, "proxyJSONRequest");
    responses.forEach((response) => {
      mock.mockImplementationOnce(() => {
        return Promise.resolve(response);
      });
    });
    return mock;
  }

  beforeEach(() => {
    vi.resetAllMocks();
    db = mockDB();
  });

  it("does nothing if index is up-to-date (304)", async () => {
    const proxyMock = mockProxyResponses([
      {
        status: 304,
        error: false,
        data: null,
        headers: new Map(),
      },
    ]);
    const status = await syncModule.syncMetadata(db, "");
    expect(proxyMock).toHaveBeenCalledTimes(1);
    expect(db.updateMetadata).not.toHaveBeenCalled();
    expect(status).toBe(SyncStatus.NOT_MODIFIED);
  });

  it("syncs and updates sources on initial sync", async () => {
    // Server index has one new source and one new item
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "abc",
      },
      items: {
        [SOURCE_UUID_2]: "def",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "ghi",
      },
    };
    const metadata: MetadataResponse = {
      sources: {
        [SOURCE_UUID_1]: mockSourceMetadata(SOURCE_UUID_1),
      },
      items: {
        [SOURCE_UUID_2]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {
        [JOURNALIST_UUID_1]: mockJournalistMetadata(JOURNALIST_UUID_1),
      },
    };
    // Client index is empty
    db = mockDB();
    const proxyMock = mockProxyResponses([
      // Index response
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      },
      // Metadata response
      {
        status: 200,
        error: false,
        data: metadata,
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    // Should update sources and items with new data
    expect(db.updateMetadata).toHaveBeenCalledWith(metadata);
  });

  it("handles error from getIndex", async () => {
    mockProxyResponses([
      {
        status: 500,
        error: true,
        data: { msg: "fail" },
        headers: new Map(),
      },
    ]);
    await expect(syncModule.syncMetadata(db, "")).rejects.toMatch(
      /Error fetching index/,
    );
  });

  it("handles error from syncMetadata", async () => {
    // getIndex returns new index
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {
        [SOURCE_UUID_2]: "v2",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v2",
      },
    };
    db = mockDB();

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      },
      {
        status: 500,
        error: true,
        data: { msg: "fail" },
        headers: new Map(),
      },
    ]);

    await expect(syncModule.syncMetadata(db, "")).rejects.toMatch(
      /Error fetching metadata from server/,
    );
    expect(db.updateMetadata).not.toHaveBeenCalled();
    expect(proxyMock).toHaveBeenCalledTimes(2);
  });

  it("reconciles index", async () => {
    // Client index has out of date item
    const clientIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v1",
      },
      items: {
        [ITEM_UUID_1]: "v1",
        [ITEM_UUID_2]: "outOfDate",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v1",
      },
    };

    // Server index doesn't have [ITEM_UUID_2]: it has been deleted
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {
        [ITEM_UUID_1]: "v2",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v2",
      },
    };
    db = mockDB({
      index: clientIndex,
    });
    const metadataToUpdate = syncModule.reconcileIndex(
      db,
      serverIndex,
      clientIndex,
    );
    expect(metadataToUpdate).toEqual({
      sources: [SOURCE_UUID_1],
      items: [ITEM_UUID_1],
      journalists: [JOURNALIST_UUID_1],
    });
  });

  it("deletes items on sync", async () => {
    // Client index has out of date item
    const clientIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v1",
      },
      items: {
        [ITEM_UUID_1]: "v1",
        [ITEM_UUID_2]: "outOfDate",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v1",
      },
    };

    // Server index doesn't have [ITEM_UUID_2]: it has been deleted
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {
        [ITEM_UUID_1]: "v2",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v2",
      },
    };
    const metadata: MetadataResponse = {
      sources: {
        [SOURCE_UUID_1]: mockSourceMetadata(SOURCE_UUID_1),
      },
      items: {
        [ITEM_UUID_1]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {
        [JOURNALIST_UUID_1]: mockJournalistMetadata(JOURNALIST_UUID_1),
      },
    };

    db = mockDB({
      index: clientIndex,
      itemFileData: {
        filename: "/securedrop/plaintext.txt",
        source_uuid: SOURCE_UUID_1,
      },
    });

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      },
      {
        status: 200,
        error: false,
        data: metadata,
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.deleteItems).toHaveBeenCalledWith([ITEM_UUID_2]);
    expect(db.updateMetadata).toHaveBeenCalledWith(metadata);
    expect(fs.rmSync).toHaveBeenCalledTimes(2);
    expect(fs.rmSync).toHaveBeenCalledWith("/securedrop/plaintext.txt", {
      force: true,
    });
    expect(fs.rmSync).toHaveBeenCalledWith(
      encryptedFilepath(SOURCE_UUID_1, ITEM_UUID_2),
      { force: true },
    );
  });

  it("reconciles partial sources", async () => {
    // Server index has updated item version
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {
        [ITEM_UUID_1]: "v2",
        [ITEM_UUID_2]: "v2",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v2",
      },
    };

    // Client index has old item version
    const clientIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {
        [ITEM_UUID_1]: "v1",
        [ITEM_UUID_2]: "v2",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "v2",
      },
    };
    db = mockDB({
      index: clientIndex,
    });

    const metadataToUpdate = syncModule.reconcileIndex(
      db,
      serverIndex,
      clientIndex,
    );
    expect(metadataToUpdate).toEqual({
      items: [ITEM_UUID_1],
      sources: [],
      journalists: [],
    });

    const metadata: MetadataResponse = {
      sources: {},
      items: {
        [ITEM_UUID_1]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {},
    };

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      },
      {
        status: 200,
        error: false,
        data: metadata,
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.updateMetadata).toHaveBeenCalledWith(metadata);
  });

  it("deletes sources on sync + updates source delta", async () => {
    // Client index has since-deleted source, and an out-of-date item
    const clientIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v1",
        [SOURCE_UUID_2]: "deleted",
      },
      items: {},
      journalists: {},
    };

    // Server index doesn't have source [SOURCE_UUID_2]: it has been deleted
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "v2",
      },
      items: {},
      journalists: {},
    };

    db = mockDB({
      index: clientIndex,
    });

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      },
      {
        status: 200,
        error: false,
        data: { sources: {}, items: {}, journalists: {} } as MetadataResponse,
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.deleteSources).toHaveBeenCalledWith([SOURCE_UUID_2]);
    expect(db.updateMetadata).toHaveBeenCalledWith({
      items: {},
      sources: {},
      journalists: {},
    });
  });
});
