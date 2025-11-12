import { describe, it, expect, vi, beforeEach, MockInstance } from "vitest";
import * as syncModule from "../../../src/main/sync";
import { DB } from "../../../src/main/database";
import {
  Index,
  ProxyJSONResponse,
  SourceMetadata,
  ItemMetadata,
  JournalistMetadata,
  SyncStatus,
  PendingEventType,
  PendingEvent,
  BatchResponse,
} from "../../../src/types";
import * as proxyModule from "../../../src/main/proxy";
import * as fs from "fs";

vi.mock("fs", () => ({
  rmSync: vi.fn(),
  existsSync: vi.fn(() => true),
  realpathSync: vi.fn((path) => path),
  mkdirSync: vi.fn(),
}));

vi.mock("os", () => ({
  default: {
    homedir: vi.fn(() => "/mock-home"),
    tmpdir: vi.fn(() => "/tmp"),
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
  pendingEvents = [],
} = {}) {
  return {
    getVersion: vi.fn(() => "v1"),
    getIndex: vi.fn(() => index),
    getItem: vi.fn((_itemID) => null),
    deleteItems: vi.fn((_itemIDs) => {}),
    deleteSources: vi.fn((_sourceIDs) => {}),
    updateBatch: vi.fn((_metadata) => {}),
    getItemFileData: vi.fn(() => itemFileData),
    getPendingEvents: vi.fn(() => pendingEvents),
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
    db = mockDB({ pendingEvents: [] });
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
    expect(db.updateBatch).not.toHaveBeenCalled();
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
    const batch: BatchResponse = {
      sources: {
        [SOURCE_UUID_1]: mockSourceMetadata(SOURCE_UUID_1),
      },
      items: {
        [SOURCE_UUID_2]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {
        [JOURNALIST_UUID_1]: mockJournalistMetadata(JOURNALIST_UUID_1),
      },
      events: {},
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
      // Batch response
      {
        status: 200,
        error: false,
        data: batch,
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    // Should update sources and items with new data
    expect(db.updateBatch).toHaveBeenCalledWith(batch);
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
      /Error fetching data from server/,
    );
    expect(db.updateBatch).not.toHaveBeenCalled();
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
      events: [],
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
    const metadata: BatchResponse = {
      sources: {
        [SOURCE_UUID_1]: mockSourceMetadata(SOURCE_UUID_1),
      },
      items: {
        [ITEM_UUID_1]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {
        [JOURNALIST_UUID_1]: mockJournalistMetadata(JOURNALIST_UUID_1),
      },
      events: {},
    };

    db = mockDB({
      index: clientIndex,
    });

    // Mock getItem to return data for ITEM_UUID_2 so cleanup can happen
    db.getItem = vi.fn((itemID: string) => {
      if (itemID === ITEM_UUID_2) {
        return {
          uuid: ITEM_UUID_2,
          filename: "/securedrop/plaintext.txt",
          data: mockItemMetadata(ITEM_UUID_2, SOURCE_UUID_1),
        };
      }
      // we only care about ITEM_UUID_2 here
      throw new Error(`Item ${itemID} not found`);
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
    expect(db.updateBatch).toHaveBeenCalledWith(metadata);
    expect(fs.rmSync).toHaveBeenCalledTimes(2);
    expect(fs.rmSync).toHaveBeenCalledWith("/securedrop/plaintext.txt", {
      force: true,
    });
    expect(fs.rmSync).toHaveBeenCalledWith(
      `/mock-home/.config/SecureDrop/files/${SOURCE_UUID_1}/${ITEM_UUID_2}/`,
      {
        recursive: true,
        force: true,
      },
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
      events: [],
    });

    const metadata: BatchResponse = {
      sources: {},
      items: {
        [ITEM_UUID_1]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {},
      events: {},
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
    expect(db.updateBatch).toHaveBeenCalledWith(metadata);
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
        data: { sources: {}, items: {}, journalists: {}, events: {} },
        headers: new Map(),
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.deleteSources).toHaveBeenCalledWith([SOURCE_UUID_2]);
    expect(db.updateBatch).toHaveBeenCalledWith({
      items: {},
      sources: {},
      journalists: {},
      events: {},
    });
  });

  it("sends pending events in batch and updates when accepted", async () => {
    // Server index is up-to-date, but there are pending events
    const pendingEvents: PendingEvent[] = [
      {
        id: "1",
        type: PendingEventType.Seen,
        target: { item_uuid: ITEM_UUID_1, version: "" },
        data: null,
      },
      {
        id: "2",
        type: PendingEventType.ItemDeleted,
        target: { item_uuid: ITEM_UUID_2, version: "" },
        data: null,
      },
    ];
    const batch: BatchResponse = {
      sources: {},
      items: {},
      journalists: {},
      events: { 1: [200, ""], 2: [200, ""] },
    };

    db = mockDB();
    db.getPendingEvents = vi.fn(() => pendingEvents);

    const proxyMock = vi.spyOn(proxyModule, "proxyJSONRequest");
    proxyMock
      // Server index has no changes
      .mockResolvedValueOnce({
        status: 304,
        error: false,
        data: null,
        headers: new Map(),
      })
      // Response with accepted pending events
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: batch,
        headers: new Map(),
      });

    const status = await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    // The batch request should include the pending events
    const batchRequestArg = proxyMock.mock.calls[1][0];
    expect(JSON.parse(batchRequestArg.body!).events).toEqual(pendingEvents);
    expect(db.updateBatch).toHaveBeenCalledWith(batch);
    expect(status).toBe(SyncStatus.UPDATED);
  });

  it("does not send batch if no server update and no pending events", async () => {
    db = mockDB();
    db.getPendingEvents = vi.fn(() => []);
    const proxyMock = vi.spyOn(proxyModule, "proxyJSONRequest");
    proxyMock.mockResolvedValueOnce({
      status: 304,
      error: false,
      data: null,
      headers: new Map(),
    });

    const status = await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(1);
    expect(db.updateBatch).not.toHaveBeenCalled();
    expect(status).toBe(SyncStatus.NOT_MODIFIED);
  });

  it("handles batch response with events and index changes", async () => {
    // Server index is up-to-date, but there are pending events
    const serverIndex: Index = {
      sources: {
        [SOURCE_UUID_1]: "abc",
      },
      items: {
        [ITEM_UUID_1]: "def",
      },
      journalists: {
        [JOURNALIST_UUID_1]: "ghi",
      },
    };
    const pendingEvents: PendingEvent[] = [
      {
        id: "1",
        type: PendingEventType.Seen,
        target: {
          item_uuid: ITEM_UUID_1,
          version: "",
        },
        data: null,
      },
    ];
    const batch: BatchResponse = {
      sources: {
        [SOURCE_UUID_1]: mockSourceMetadata(SOURCE_UUID_1),
      },
      items: {
        [ITEM_UUID_1]: mockItemMetadata(ITEM_UUID_1, SOURCE_UUID_1),
      },
      journalists: {
        [JOURNALIST_UUID_1]: mockJournalistMetadata(JOURNALIST_UUID_1),
      },
      events: { 1: [200, ""] },
    };

    db = mockDB();
    db.getPendingEvents = vi.fn(() => pendingEvents);

    const proxyMock = vi.spyOn(proxyModule, "proxyJSONRequest");
    proxyMock
      // Index response
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: serverIndex,
        headers: new Map(),
      })
      // Batch response
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: batch,
        headers: new Map(),
      });

    const status = await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.updateBatch).toHaveBeenCalledWith(batch);
    expect(status).toBe(SyncStatus.UPDATED);
  });
});
