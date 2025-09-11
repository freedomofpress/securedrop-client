import { describe, it, expect, vi, beforeEach } from "vitest";
import { FetchStatus } from "../../types";
import { DB } from "../database";
import { BufferedWriter } from "./bufferedWriter";

// Mocks
const mockProxyStreamRequest = vi.hoisted(() => {
  return vi.fn();
});
vi.mock("../proxy", async () => {
  const actual = await vi.importActual("../proxy");
  return {
    ...actual,
    proxyStreamRequest: mockProxyStreamRequest,
  };
});

import { ItemFetchTask, TaskQueue } from "./queue";

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function mockDB(itemsToDownload: string[], itemsWithFetchStatus: any[]) {
  return {
    getItemsToDownload: vi.fn(() => itemsToDownload),
    getItemWithFetchStatus: vi.fn(() => itemsWithFetchStatus),
    updateInProgressItem: vi.fn(),
    completePlaintextItem: vi.fn(),
    completeFileItem: vi.fn(),
    failItem: vi.fn(),
  } as unknown as DB;
}

function mockFetchDownload(_task: ItemFetchTask, _db: DB): void {
  return;
}

describe("TaskQueue", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it("should queue fetches for items to download", () => {
    const db = mockDB(["item1", "item2"], []);
    const queue = new TaskQueue(db, mockFetchDownload);
    vi.spyOn(queue.queue, "push");
    queue.queueFetches({ authToken: "token" });
    expect(queue.authToken).toBe("token");
    expect(queue.queue.push).toHaveBeenCalledTimes(2);
    expect(queue.queue.push).toHaveBeenCalledWith(
      { id: "item1" },
      expect.any(Function),
    );
    expect(queue.queue.push).toHaveBeenCalledWith(
      { id: "item2" },
      expect.any(Function),
    );
  });

  it("should handle message download and completePlaintextItem", async () => {
    const db = mockDB(
      [],
      [{ kind: "message", source: "source1" }, FetchStatus.InProgress, 0],
    );

    const queue = new TaskQueue(db, mockFetchDownload);
    mockProxyStreamRequest.mockResolvedValue({
      complete: true,
      bytesWritten: 50,
    });

    const buf = {
      toString: vi.fn().mockReturnValue("msg"),
    } as unknown as Buffer;
    queue["db"].completePlaintextItem = vi.fn();
    vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(buf);
    await queue.fetchDownload({ id: "item2" }, db);
    expect(queue.db.completePlaintextItem).toHaveBeenCalledWith("item2", "msg");
  });

  it("should handle reply download and completePlaintextItem", async () => {
    const db = mockDB(
      [],
      [{ kind: "reply", source: "source1" }, FetchStatus.InProgress, 0],
    );

    const queue = new TaskQueue(db, mockFetchDownload);
    mockProxyStreamRequest.mockResolvedValue({
      complete: true,
      bytesWritten: 50,
    });

    const buf = {
      toString: vi.fn().mockReturnValue("replymsg"),
    } as unknown as Buffer;
    queue["db"].completePlaintextItem = vi.fn();
    vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(buf);
    await queue.fetchDownload({ id: "item1" }, db);
    expect(queue.db.completePlaintextItem).toHaveBeenCalledWith(
      "item1",
      "replymsg",
    );
  });

  it("should update in-progress item and throw if download incomplete", async () => {
    const db = mockDB(
      [],
      [{ kind: "message", source: "src" }, FetchStatus.InProgress, 20],
    );
    const queue = new TaskQueue(db, mockFetchDownload);
    mockProxyStreamRequest.mockResolvedValue({
      complete: false,
      bytesWritten: 30,
    });
    await expect(queue.fetchDownload({ id: "item3" }, db)).rejects.toThrow(
      /Unable to complete stream download/,
    );
    expect(queue.db.updateInProgressItem).toHaveBeenCalledWith("item3", 50);
  });
});
