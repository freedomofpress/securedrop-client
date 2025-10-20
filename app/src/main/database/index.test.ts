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

    db.addPendingReplySentEvent(
      "item4",
      "here is a reply",
      "source1",
      "journalist",
    );
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(4);
    const reply = sourceWithItems.items.find((i) => {
      return i.uuid === "item4";
    });
    expect(reply?.plaintext === "this is a reply");
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

    db.addPendingReplySentEvent("item3", "reply text", "source1", "journalist");
    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(3);

    db.addPendingSourceEvent(
      "source1",
      PendingEventType.SourceConversationDeleted,
    );
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(0);
  });

  it("pending SourceConversationDeleted and ReplySent should show reply", () => {
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

    const snowflake2 = db.addPendingReplySentEvent(
      "item3",
      "reply text",
      "source1",
      "journalist",
    );
    expect(snowflake2 > snowflake1);
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(1);
    expect(sourceWithItems.items[0].uuid).toBe("item3");
    expect(sourceWithItems.items[0].plaintext).toBeDefined();
  });

  it("pending ReplySent and then pending SourceDeleted should delete source", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    db.updateItems({
      item1: mockItemMetadata("item1", "source1"),
    });

    db.addPendingReplySentEvent("item2", "reply text", "source1", "journalist");
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

    db.addPendingReplySentEvent("item2", "reply text", "source1", "journalist");
    let sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(2);

    db.addPendingItemEvent("item2", PendingEventType.ItemDeleted);
    sourceWithItems = db.getSourceWithItems("source1");
    expect(sourceWithItems.items.length).toEqual(1);
    expect(
      sourceWithItems.items.find((i) => i.uuid === "item2"),
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

    const snowflakeIds = db.addPendingItemsSeenBatch("source1");

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
    const firstCallIds = db.addPendingItemsSeenBatch("source1");
    expect(firstCallIds.length).toEqual(3);

    // Second call should create 0 events (all items already have Seen events)
    const secondCallIds = db.addPendingItemsSeenBatch("source1");
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
    const firstCallIds = db.addPendingItemsSeenBatch("source1");
    expect(firstCallIds.length).toEqual(2);

    // Add a new item
    db.updateItems({
      item3: mockItemMetadata("item3", "source1"),
    });

    // Second call should only create event for the new item
    const secondCallIds = db.addPendingItemsSeenBatch("source1");
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
    const source1Ids = db.addPendingItemsSeenBatch("source1");
    expect(source1Ids.length).toEqual(2);

    // source2 items should still be unseen
    const source2Ids = db.addPendingItemsSeenBatch("source2");
    expect(source2Ids.length).toEqual(2);
  });

  it("addPendingItemsSeenBatch should return empty array for source with no items", () => {
    db.updateSources({
      source1: mockSourceMetadata("source1"),
    });

    const snowflakeIds = db.addPendingItemsSeenBatch("source1");
    expect(snowflakeIds.length).toEqual(0);
  });
});
