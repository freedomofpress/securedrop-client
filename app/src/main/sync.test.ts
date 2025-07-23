import { describe, it, expect, vi, beforeEach, MockInstance } from "vitest";
import * as syncModule from "../../src/main/sync";
import { DB } from "../../src/main/database";
import type { Index, ProxyJSONResponse } from "../../src/types";
import * as proxyModule from "../../src/main/proxy";

function mockDB({
  version = "v1",
  index = { sources: {} },
  itemVersions = {},
  updateSources = vi.fn(),
} = {}) {
  return {
    getVersion: vi.fn(() => version),
    getIndex: vi.fn(() => index),
    getSourceItemVersions: vi.fn((uuid) => itemVersions[uuid] || {}),
    updateSources,
  } as unknown as DB;
}

describe("syncMetadata", () => {
  let db: DB;

  function mockProxyResponses<T>(
    responses: ProxyJSONResponse<T>[],
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
    expect(db.updateSources).not.toHaveBeenCalled();
    expect(status).toBe(syncModule.SyncStatus.NOT_MODIFIED);
  });

  it("syncs and updates sources on initial sync", async () => {
    // Server index has one new source
    const serverIndex: Index = {
      sources: {
        uuid1: {
          version: "abc",
          collection: { foo: "bar" },
        },
      },
    };
    // Client index is empty
    db = mockDB({ index: { sources: {} }, updateSources: vi.fn() });
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
        data: {
          sources: { uuid1: { version: "abc", collection: { foo: "bar" } } },
        },
        headers: {} as Map<string, string>,
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    // Should update sources with new data
    expect(db.updateSources).toHaveBeenCalledWith({
      sources: { uuid1: { version: "abc", collection: { foo: "bar" } } },
    });
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
        uuid1: {
          version: "v2",
          collection: { item1: "v2" },
        },
      },
    };
    db = mockDB({ index: { sources: {} }, updateSources: vi.fn() });

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
        // @ts-expect-error: typecheck
        data: { msg: "fail" },
        headers: {} as Map<string, string>,
      },
    ]);

    await expect(syncModule.syncMetadata(db, "")).rejects.toMatch(
      /Error fetching synchronized sources from server/,
    );
    expect(db.updateSources).not.toHaveBeenCalled();
    expect(proxyMock).toHaveBeenCalledTimes(2);
  });

  it("reconciles partial sources", async () => {
    // Server index has updated item version
    const serverIndex: Index = {
      sources: {
        uuid1: {
          version: "v2",
          collection: { item1: "v2", item2: "v1" },
        },
      },
    };

    // Client index has old item version
    const clientIndex: Index = {
      sources: {
        uuid1: {
          version: "v1",
          collection: { item1: "v1", item2: "v1" },
        },
      },
    };
    db = mockDB({
      index: clientIndex,
      itemVersions: { uuid1: { item1: "v1", item2: "v1" } },
      updateSources: vi.fn(),
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
        data: {
          sources: {
            uuid1: { version: "v2", collection: { item1: "v2", item2: "v1" } },
          },
        },
        headers: {} as Map<string, string>,
      },
    ]);

    await syncModule.syncMetadata(db, "");

    expect(proxyMock).toHaveBeenCalledTimes(2);
    expect(db.updateSources).toHaveBeenCalledWith({
      sources: {
        uuid1: { version: "v2", collection: { item1: "v2", item2: "v1" } },
      },
    });
  });
});
