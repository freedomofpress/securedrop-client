import { describe, expect, it, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { DB } from "./index";
import { ItemMetadata, PendingEventType, SourceMetadata } from "../../types";

describe("Database Component Tests", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home");
  const testDbDir = path.join(testHomeDir, ".config", "SecureDrop");
  const testDbPath = path.join(testDbDir, "db.sqlite");
  const originalHomedir = os.homedir;
  let db: DB;

  beforeEach(() => {
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
  });

  afterEach(() => {
    if (db) {
      db.close();
    }
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  it("should create database with correct setup", () => {
    db = new DB();

    expect(db).toBeDefined();
    expect(fs.existsSync(testDbPath)).toBe(true);
    expect(db["db"]!.pragma("journal_mode", { simple: true })).toBe("wal");
  });

  it("should handle database closure", () => {
    db = new DB();
    expect(db).toBeDefined();

    db.close();
    expect(() => db.close()).not.toThrow();
  });

  it("should create valid database file", () => {
    db = new DB();
    const stats = fs.statSync(testDbPath);
    expect(stats.isFile()).toBe(true);
    expect(stats.size).toBeGreaterThan(0);
  });
});

describe("pending_events update projected views", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home");
  const originalHomedir = os.homedir;
  let db: DB;

  beforeEach(() => {
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
    db = new DB();
  });

  afterEach(() => {
    if (db) {
      db.close();
    }
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  function mockSourceMetadata(
    uuid: string,
    is_starred?: boolean,
  ): SourceMetadata {
    return {
      uuid: uuid,
      journalist_designation: "Foo Bar",
      is_starred: is_starred ?? false,
      is_seen: false,
      has_attachment: false,
      last_updated: "",
      public_key: "",
      fingerprint: "",
    };
  }

  function mockItemMetadata(uuid: string, source_uuid: string): ItemMetadata {
    return {
      kind: "reply",
      uuid: uuid,
      source: source_uuid,
      size: 50,
      journalist_uuid: "",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: 1,
    };
  }

  it("pending SourceDeleted event should remove source in getSources", () => {
    // Insert three sources
    db.updateSources({
      source1: mockSourceMetadata("source1"),
      source2: mockSourceMetadata("source2"),
      source3: mockSourceMetadata("source3"),
    });

    let sources = db.getSources();
    expect(sources.length).toEqual(3);
    expect(sources.map((s) => s.uuid)).toEqual([
      "source1",
      "source2",
      "source3",
    ]);

    // Add pending delete for source3
    db.addPendingSourceEvent("source3", PendingEventType.SourceDeleted);

    // getSources should now return only source1, source2
    sources = db.getSources();
    expect(sources.length).toEqual(2);
    expect(sources.map((s) => s.uuid)).toEqual(["source1", "source2"]);
  });

  it("pending SourceConversationDeleted should remove all items", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingSourceEvent(
      "source1",
      PendingEventType.SourceConversationDeleted,
    );
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(0);

    db.updateSources({
      source2: mockSourceMetadata("source2"),
    });
  });

  it("pending SourceConversationDeleted event should only affect given source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingSourceEvent(
      "source1",
      PendingEventType.SourceConversationDeleted,
    );
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(0);

    // Add source2 with 3 items
    db.updateSources({
      source2: mockSourceMetadata("source2"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source2"),
      item2: mockItemMetadata("item2", "source2"),
      item3: mockItemMetadata("item3", "source2"),
    });
    sourceWithItems = db.getSourceWithItems("source2");
    expect(sourceWithItems.items.length).toEqual(3);
  });

  it("pending Starred event should star sources", () => {
    // Insert three sources
    db.updateSources({
      source1: mockSourceMetadata("source1"),
      source2: mockSourceMetadata("source2"),
      source3: mockSourceMetadata("source3"),
    });
    let sources = db.getSources();
    for (const source of sources) {
      expect(source.data.is_starred).toBe(false);
    }

    db.addPendingSourceEvent("source1", PendingEventType.Starred);
    db.addPendingSourceEvent("source2", PendingEventType.Starred);

    sources = db.getSources();
    for (const source of sources) {
      if (source.uuid === "source1" || source.uuid === "source2") {
        expect(source.data.is_starred).toBeTruthy();
        continue;
      }
      expect(source.data.is_starred).toBe(false);
    }
  });

  it("pending Unstarred event should unstar source", () => {
    // Insert three sources
    db.updateSources({
      source1: mockSourceMetadata("source1", true),
      source2: mockSourceMetadata("source2", true),
      source3: mockSourceMetadata("source3", true),
    });
    let sources = db.getSources();
    for (const source of sources) {
      expect(source.data.is_starred).toBe(true);
    }

    db.addPendingSourceEvent("source1", PendingEventType.Unstarred);
    db.addPendingSourceEvent("source2", PendingEventType.Unstarred);

    sources = db.getSources();
    for (const source of sources) {
      if (source.uuid === "source1" || source.uuid === "source2") {
        expect(source.data.is_starred).toBeFalsy();
        continue;
      }
      expect(source.data.is_starred).toBe(true);
    }
  });

  it("multiple Star/Unstarred events should project latest", () => {
    // Insert three sources
    db.updateSources({
      source1: mockSourceMetadata("source1", true),
      source2: mockSourceMetadata("source2", true),
      source3: mockSourceMetadata("source3", true),
    });
    let sources = db.getSources();
    for (const source of sources) {
      expect(source.data.is_starred).toBe(true);
    }

    db.addPendingSourceEvent("source1", PendingEventType.Unstarred);
    db.addPendingSourceEvent("source1", PendingEventType.Starred);

    sources = db.getSources();
    for (const source of sources) {
      if (source.uuid === "source1") {
        expect(source.data.is_starred).toBeTruthy();
        continue;
      }
      expect(source.data.is_starred).toBe(true);
    }

    db.addPendingSourceEvent("source1", PendingEventType.Unstarred);
    sources = db.getSources();
    for (const source of sources) {
      if (source.uuid === "source1") {
        expect(source.data.is_starred).toBeFalsy();
        continue;
      }
      expect(source.data.is_starred).toBe(true);
    }
  });

  it("pending Seen event should mark seen", () => {
    // Insert three sources
    db.updateSources({
      source1: mockSourceMetadata("source1", true),
      source2: mockSourceMetadata("source2", true),
      source3: mockSourceMetadata("source3", true),
    });
    let sources = db.getSources();
    for (const source of sources) {
      expect(source.isRead).toBe(false);
    }

    db.addPendingSourceEvent("source1", PendingEventType.Seen);
    sources = db.getSources();
    for (const source of sources) {
      if (source.uuid === "source1") {
        expect(source.isRead).toBe(true);
        continue;
      }
      expect(source.isRead).toBe(false);
    }
  });

  it("pending ReplySent event should add reply", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingReplySentEvent("here is a reply", "source1", 4);
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(4);
    const reply = sourceWithItems.items[3];
    expect(reply?.plaintext).toBe("here is a reply");
  });

  it("getSourceWithItems returns items sorted by interaction_count", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item3: {
        ...mockItemMetadata("item3", "source1"),
        interaction_count: 3,
      },
      item1: {
        ...mockItemMetadata("item1", "source1"),
        interaction_count: 1,
      },
      item5: {
        ...mockItemMetadata("item5", "source1"),
        interaction_count: 5,
      },
      item2: {
        ...mockItemMetadata("item2", "source1"),
        interaction_count: 2,
      },
      item4: {
        ...mockItemMetadata("item4", "source1"),
        interaction_count: 4,
      },
    });

    const sourceWithItems = db.getSourceWithItems("source1");
    const items = sourceWithItems.items;

    // Clone and sort by interaction_count
    const sortedItems = [...items].sort(
      (a, b) => a.data.interaction_count - b.data.interaction_count,
    );

    // Verify the returned items are already sorted
    expect(items).toEqual(sortedItems);
  });

  it("pending ItemDeleted event should delete reply", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingItemEvent("item1", PendingEventType.ItemDeleted);

    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(2);
  });

  it("pending ReplySent and pending SourceConversationDeleted should delete all items in conversation", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
    });

    db.addPendingReplySentEvent("reply text", "source1", 3);
    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingSourceEvent(
      "source1",
      PendingEventType.SourceConversationDeleted,
    );
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(0);
  });

  it("pending SourceConversationDeleted and ReplySent should show reply", async () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
    });

    const snowflake1 = db.addPendingSourceEvent(
      "source1",
      PendingEventType.SourceConversationDeleted,
    );
    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(0);

    const snowflake2 = await db.addPendingReplySentEvent(
      "reply text",
      "source1",
      1,
    );
    expect(snowflake2 > snowflake1);
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(1);
    expect(sourceWithItems.items[0].uuid).toMatch(
      /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i,
    );
    expect(sourceWithItems.items[0].plaintext).toBe("reply text");
  });

  it("pending ReplySent and then pending SourceDeleted should delete source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    db.addPendingReplySentEvent("reply text", "source1", 1);
    let sources = db.getSources();
    expect(sources.length).toEqual(1);

    db.addPendingSourceEvent("source1", PendingEventType.SourceDeleted);
    sources = db.getSources();
    expect(sources.length).toEqual(0);
  });

  it("pending ReplySent and then pending ItemDeleted should delete reply", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    db.addPendingReplySentEvent("reply text", "source1", 2);
    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(2);
    const pendingReplyUuid = sourceWithItems.items[1].uuid;

    db.addPendingItemEvent(pendingReplyUuid, PendingEventType.ItemDeleted);
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(1);
    expect(
      sourceWithItems.items.find((i) => i.uuid === pendingReplyUuid),
    ).toBeUndefined();
  });

  it("pending multiple ItemDeleted events should delete all specified items", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    db.addPendingItemEvent("item1", PendingEventType.ItemDeleted);
    db.addPendingItemEvent("item3", PendingEventType.ItemDeleted);

    const sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(1);
    expect(sourceWithItems.items[0].uuid).toBe("item2");
  });

  it("addPendingItemsSeenBatch should create Seen events for all items in source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    const snowflakeIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
      "item3",
    ]);

    // Should create 3 events for 3 items
    expect(snowflakeIds.length).toEqual(3);

    // All snowflake IDs should be unique
    const uniqueIds = new Set(snowflakeIds);
    expect(uniqueIds.size).toEqual(3);
  });

  it("addPendingItemsSeenBatch should be idempotent - no duplicates on second call", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    // First call should create 3 events
    const firstCallIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
      "item3",
    ]);
    expect(firstCallIds.length).toEqual(3);

    // Second call should create 0 events (all items already have Seen events)
    const secondCallIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
      "item3",
    ]);
    expect(secondCallIds.length).toEqual(0);
  });

  it("addPendingItemsSeenBatch should only create events for new items after sync", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
    });

    // First call creates events for 2 items
    const firstCallIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
    ]);
    expect(firstCallIds.length).toEqual(2);

    // Add a new item
    db.updateItems({
      item3: mockItemMetadata("item3", "source1"),
    });

    // Second call should only create event for the new item
    const secondCallIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
      "item3",
    ]);
    expect(secondCallIds.length).toEqual(1);
  });

  it("addPendingItemsSeenBatch should only affect specified source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
      source2: mockSourceMetadata("source2"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source2"),
      item4: mockItemMetadata("item4", "source2"),
    });

    // Mark source1 items as seen
    const source1Ids = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
    ]);
    expect(source1Ids.length).toEqual(2);

    // source2 items should still be unseen
    const source2Ids = db.addPendingItemsSeenBatch("source2", [
      "item3",
      "item4",
    ]);
    expect(source2Ids.length).toEqual(2);
  });

  it("addPendingItemsSeenBatch should return empty array for source with no items", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    const snowflakeIds = db.addPendingItemsSeenBatch("source1", []);
    expect(snowflakeIds.length).toEqual(0);
  });

  it("addPendingItemsSeenBatch should only create events for specified items", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
      item3: mockItemMetadata("item3", "source1"),
    });

    // Only mark item1 and item3 as seen, not item2
    const snowflakeIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item3",
    ]);

    // Should only create 2 events
    expect(snowflakeIds.length).toEqual(2);

    // Calling again with all items should only create event for item2
    const secondCallIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
      "item3",
    ]);
    expect(secondCallIds.length).toEqual(1);
  });

  it("addPendingItemsSeenBatch should handle empty itemUuids array", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source1"),
    });

    // Passing empty array should create no events
    const snowflakeIds = db.addPendingItemsSeenBatch("source1", []);
    expect(snowflakeIds.length).toEqual(0);
  });

  it("addPendingItemsSeenBatch should ignore items not in the source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
      source2: mockSourceMetadata("source2"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
      item2: mockItemMetadata("item2", "source2"),
    });

    // Try to mark item2 as seen, but it belongs to source2
    const snowflakeIds = db.addPendingItemsSeenBatch("source1", [
      "item1",
      "item2",
    ]);

    // Should only create event for item1
    expect(snowflakeIds.length).toEqual(1);
  });

  it("getPendingEvents should return all pending events with correct structure", async () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });
    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    const snowflakeSource = db.addPendingSourceEvent(
      "source1",
      PendingEventType.Starred,
    );
    console.log("source Snowflake: ", snowflakeSource);
    const snowflakeItem = db.addPendingItemEvent(
      "item1",
      PendingEventType.ItemDeleted,
    );
    const snowflakeReply = await db.addPendingReplySentEvent(
      "reply text",
      "source1",
      1,
    );

    const events = db.getPendingEvents();
    expect(events.length).toBe(3);
    console.log("events: ", events);

    const sourceEvent = events.find((e) => e.id === snowflakeSource);
    expect(sourceEvent).toBeDefined();
    expect(sourceEvent!.type).toBe(PendingEventType.Starred);
    expect(sourceEvent!.target).toHaveProperty("source_uuid", "source1");

    const itemEvent = events.find((e) => e.id === snowflakeItem);
    expect(itemEvent).toBeDefined();
    expect(itemEvent!.type).toBe(PendingEventType.ItemDeleted);
    expect(itemEvent!.target).toHaveProperty("item_uuid", "item1");

    const replyEvent = events.find((e) => e.id === snowflakeReply);
    expect(replyEvent).toBeDefined();
    expect(replyEvent!.type).toBe(PendingEventType.ReplySent);
    expect(replyEvent!.target).toHaveProperty("source_uuid");
    expect(replyEvent!.data).toHaveProperty("metadata");
    expect(replyEvent!.data).toHaveProperty("plaintext", "reply text");
  });

  it("updatePendingEvents should remove successful events from pending_events", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });
    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    // Verify source and item exist
    const sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems).toBeDefined();
    expect(sourceWithItems.uuid).toEqual("source1");
    expect(sourceWithItems.items.length).toBe(1);
    expect(sourceWithItems.items[0].uuid).toBe("item1");

    const snowflakeSource = db.addPendingSourceEvent(
      "source1",
      PendingEventType.Starred,
    );
    const snowflakeItem = db.addPendingItemEvent(
      "item1",
      PendingEventType.ItemDeleted,
    );

    // Before update, both events are present
    let events = db.getPendingEvents();
    expect(events.length).toBe(2);

    // Simulate server response: both events succeeded (HTTP 200)
    db.updatePendingEvents({
      [snowflakeSource.toString()]: [200, ""],
      [snowflakeItem.toString()]: [200, ""],
    });

    // After update, no pending events should remain
    events = db.getPendingEvents();
    expect(events.length).toBe(0);
  });

  it("updatePendingEvents should retain failed events", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });
    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    const snowflakeSource = db.addPendingSourceEvent(
      "source1",
      PendingEventType.Starred,
    );
    const snowflakeItem = db.addPendingItemEvent(
      "item1",
      PendingEventType.ItemDeleted,
    );

    // Simulate server response: only one event succeeded
    db.updatePendingEvents({
      [snowflakeSource.toString()]: [200, ""],
      [snowflakeItem.toString()]: [500, "error"], // failed
    });

    const events = db.getPendingEvents();
    expect(events.length).toBe(1);
    expect(events[0].id).toBe(snowflakeItem);
    expect(events[0].type).toBe(PendingEventType.ItemDeleted);
  });
});
