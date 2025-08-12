import { describe, it, expect, vi, beforeEach, MockInstance } from "vitest";
import * as syncModule from "../../src/main/sync";
import { DB } from "../../src/main/database";
import type {
  Index,
  ProxyJSONResponse,
  MetadataResponse,
  SourceMetadata,
  ItemMetadata,
} from "../../src/types";
import * as proxyModule from "../../src/main/proxy";

function mockDB({ index = { sources: {}, items: {} } } = {}) {
  return {
    getVersion: vi.fn(() => "v1"),
    getIndex: vi.fn(() => index),
    deleteItems: vi.fn((_itemIDs) => {}),
    deleteSources: vi.fn((_sourceIDs) => {}),
    updateMetadata: vi.fn((_metadata) => {}),
  } as unknown as DB;
}

function mockSourceMetadata(uuid: string): SourceMetadata {
  return {
    uuid: uuid,
    journalist_designation: "Test Journalist",
    is_starred: false,
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
    journalist_uuid: "test_journalist",
    is_deleted_by_source: false,
    seen_by: [],
  };
}

describe("syncMetadata", () => {
  let db: DB;

  function mockProxyResponses(
    responses: ProxyJSONResponse<any>[], // eslint-disable-line @typescript-eslint/no-explicit-any
  ): MockInstance {
    const mock = vi.spyOn(proxyModule, "proxy");
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
        headers: {} as Map<string, string>,
      },
    ]);
    const status = await syncModule.syncMetadata(db, "");
    expect(proxyMock).toHaveBeenCalledTimes(1);
    expect(db.updateMetadata).not.toHaveBeenCalled();
    expect(status).toBe(syncModule.SyncStatus.NOT_MODIFIED);
  });

  it("syncs and updates sources on initial sync", async () => {
    // Server index has one new source and one new item
    const serverIndex: Index = {
      sources: {
        uuid1: "abc",
      },
      items: {
        uuid2: "def",
      },
      journalists: {},
    };
    const metadata: MetadataResponse = {
      sources: {
        uuid1: mockSourceMetadata("uuid1"),
      },
      items: {
        uuid2: mockItemMetadata("uuid2", "uuid1"),
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
        headers: {} as Map<string, string>,
      },
      // Metadata response
      {
        status: 200,
        error: false,
        data: metadata,
        headers: {} as Map<string, string>,
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
        headers: {} as Map<string, string>,
      },
    ]);
    await expect(syncModule.syncMetadata(db, "")).rejects.toMatch(
      /Error fetching index/,
    );
  });

  it("handles error from syncSources", async () => {
    // getIndex returns new index
    const serverIndex: Index = {
      sources: {
        uuid1: "v2",
      },
      items: {
        uuid2: "v2",
      },
      journalists: {},
    };
    db = mockDB();

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: {} as Map<string, string>,
      },
      {
        status: 500,
        error: true,
        data: { msg: "fail" },
        headers: {} as Map<string, string>,
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
        source1: "v1",
      },
      items: {
        item1: "v1",
        item2: "outOfDate",
      },
      journalists: {},
    };

    // Server index doesn't have item2: it has been deleted
    const serverIndex: Index = {
      sources: {
        source1: "v2",
      },
      items: {
        item1: "v2",
      },
      journalists: {},
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
      sources: ["source1"],
      items: ["item1"],
    });
  });

  it("deletes items on sync", async () => {
    // Client index has out of date item
    const clientIndex: Index = {
      sources: {
        source1: "v1",
      },
      items: {
        item1: "v1",
        item2: "outOfDate",
      },
      journalists: {},
    };

    // Server index doesn't have item2: it has been deleted
    const serverIndex: Index = {
      sources: {
        source1: "v2",
      },
      items: {
        item1: "v2",
      },
      journalists: {},
    };
    const metadata: MetadataResponse = {
      sources: {
        source1: mockSourceMetadata("source1"),
      },
      items: {
        item1: mockItemMetadata("item1", "source1"),
      },
    };

    db = mockDB({
      index: clientIndex,
    });

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: {} as Map<string, string>,
      },
      {
        status: 200,
        error: false,
        data: metadata,
        headers: {} as Map<string, string>,
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.deleteItems).toHaveBeenCalledWith(["item2"]);
    expect(db.updateMetadata).toHaveBeenCalledWith(metadata);
  });

  it("reconciles partial sources", async () => {
    // Server index has updated item version
    const serverIndex: Index = {
      sources: {
        source1: "v2",
      },
      items: {
        item1: "v2",
        item2: "v2",
      },
      journalists: {},
    };

    // Client index has old item version
    const clientIndex: Index = {
      sources: {
        source1: "v2",
      },
      items: {
        item1: "v1",
        item2: "v2",
      },
      journalists: {},
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
      items: ["item1"],
      sources: [],
    });

    const metadata: MetadataResponse = {
      sources: {},
      items: {
        item1: mockItemMetadata("item1", "source1"),
      },
    };

    const proxyMock = mockProxyResponses([
      {
        status: 200,
        error: false,
        data: serverIndex,
        headers: {} as Map<string, string>,
      },
      {
        status: 200,
        error: false,
        data: metadata,
        headers: {} as Map<string, string>,
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
        uuid1: "v1",
        uuid2: "deleted",
      },
      items: {},
      journalists: {},
    };

    // Server index doesn't have source uuid2: it has been deleted
    const serverIndex: Index = {
      sources: {
        uuid1: "v2",
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
        headers: {} as Map<string, string>,
      },
      {
        status: 200,
        error: false,
        data: { sources: {}, items: {} } as MetadataResponse,
        headers: {} as Map<string, string>,
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.deleteSources).toHaveBeenCalledWith(["uuid2"]);
    expect(db.updateMetadata).toHaveBeenCalledWith({
      items: {},
      sources: {},
    });
  });
});
