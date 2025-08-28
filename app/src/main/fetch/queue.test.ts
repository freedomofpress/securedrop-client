import { vi, describe, it, expect, beforeEach, afterEach, test } from "vitest";
import * as queueModule from "./queue";
import { FetchStatus } from "../../types";
import Queue from "better-queue";
import { DB } from "../database";

const mockGetItemsToDownload = vi.fn();
const mockGetItemFetchStatus = vi.fn();
const mockCompletePlaintextItem = vi.fn();
const mockFailItem = vi.fn();

function mockDB(): DB {
  return {
    getItemsToDownload: mockGetItemsToDownload,
    getItemFetchStatus: mockGetItemFetchStatus,
    completePlaintextItem: mockCompletePlaintextItem,
    failItem: mockFailItem,
  } as unknown as DB;
}

describe("fetch/worker", () => {
  let queue: Queue;
  let db: DB;

  beforeEach(() => {
    vi.clearAllMocks();
    vi.resetModules();
    queue = new Queue(() => {}, {});
    db = mockDB();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("should queue items to be fetched from DB", async () => {
    vi.spyOn(queue, "push");
    mockGetItemsToDownload.mockReturnValue(["item1", "item2"]);
    mockGetItemFetchStatus.mockReturnValue([FetchStatus.InProgress, 0]);

    queueModule.queueFetches(db, queue);
    expect(mockGetItemsToDownload).toHaveBeenCalled();

    // Should push both items to the queue
    expect(queue.push).toHaveBeenCalledTimes(2);
    expect(queue.push).toHaveBeenCalledWith({ id: "item1" });
    expect(queue.push).toHaveBeenCalledWith({ id: "item2" });
  });

  test.each(["item1", "item2", "paused", "complete"])(
    "should skip fetching items that are already complete, failed, or paused",
    async (itemID: string) => {
      mockGetItemFetchStatus.mockImplementation((id: string) => {
        if (id === "paused") {
          return [FetchStatus.Paused, 0];
        }
        if (id === "complete") {
          return [FetchStatus.Complete, 0];
        }
        return [FetchStatus.Initial, 0];
      });

      await queueModule.fetchDownload({ id: itemID }, db);
      if (itemID === "paused" || itemID === "complete") {
        expect(db.completePlaintextItem).toHaveBeenCalledTimes(0);
      } else {
        expect(db.completePlaintextItem).toHaveBeenCalledWith(itemID, "");
      }
    },
  );
});
