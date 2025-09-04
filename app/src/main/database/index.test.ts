import { describe, expect, it, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { DB } from "./index";
import type { MetadataResponse } from "../../types";

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

  it("should update message item with plaintext", () => {
    db = new DB();

    // First, insert a message item to update
    const itemId = "test-message-uuid";
    const itemMetadata = {
      kind: "message" as const,
      uuid: itemId,
      source: "test-source-uuid",
      size: 1024,
      is_read: false,
      seen_by: [],
    };

    db.updateMetadata({
      sources: {},
      items: {
        [itemId]: itemMetadata,
      },
      journalists: {},
    });

    // Update the message item with plaintext content
    const plaintext = "Decrypted message content";

    expect(() => {
      db.updateItem(itemId, { plaintext });
    }).not.toThrow();

    // Verify the update by checking the database directly
    const result = db["db"]!.prepare(
      "SELECT plaintext, filename FROM items WHERE uuid = ?",
    ).get(itemId) as {
      plaintext: string;
      filename: string | null;
    };

    expect(result.plaintext).toBe(plaintext);
    expect(result.filename).toBeNull();
  });

  it("should update file item with filename", () => {
    db = new DB();

    // First, insert a file item to update
    const itemId = "test-file-uuid";
    const itemMetadata = {
      kind: "file" as const,
      uuid: itemId,
      source: "test-source-uuid",
      size: 2048,
      is_read: false,
      seen_by: [],
    };

    db.updateMetadata({
      sources: {},
      items: {
        [itemId]: itemMetadata,
      },
      journalists: {},
    });

    // Update the file item with filename
    const filename = "document.pdf";

    expect(() => {
      db.updateItem(itemId, { filename });
    }).not.toThrow();

    // Verify the update by checking the database directly
    const result = db["db"]!.prepare(
      "SELECT plaintext, filename FROM items WHERE uuid = ?",
    ).get(itemId) as {
      plaintext: string | null;
      filename: string;
    };

    expect(result.plaintext).toBeNull();
    expect(result.filename).toBe(filename);
  });

  it("should update reply item with plaintext", () => {
    db = new DB();

    // First, insert a reply item to update
    const itemId = "test-reply-uuid";
    const itemMetadata = {
      kind: "reply" as const,
      uuid: itemId,
      source: "test-source-uuid",
      size: 1024,
      journalist_uuid: "journalist-uuid",
      is_deleted_by_source: false,
      seen_by: [],
    };

    db.updateMetadata({
      sources: {},
      items: {
        [itemId]: itemMetadata,
      },
      journalists: {},
    });

    // Update the reply item with plaintext content
    const plaintext = "Decrypted reply content";

    expect(() => {
      db.updateItem(itemId, { plaintext });
    }).not.toThrow();

    // Verify the update by checking the database directly
    const result = db["db"]!.prepare(
      "SELECT plaintext, filename FROM items WHERE uuid = ?",
    ).get(itemId) as {
      plaintext: string;
      filename: string | null;
    };

    expect(result.plaintext).toBe(plaintext);
    expect(result.filename).toBeNull();
  });

  it("should reject plaintext update for file items", () => {
    db = new DB();

    // Insert a file item
    const itemId = "test-file-uuid";
    const itemMetadata = {
      kind: "file" as const,
      uuid: itemId,
      source: "test-source-uuid",
      size: 2048,
      is_read: false,
      seen_by: [],
    };

    db.updateMetadata({
      sources: {},
      items: {
        [itemId]: itemMetadata,
      },
      journalists: {},
    });

    // Try to update plaintext on a file item - should throw
    expect(() => {
      db.updateItem(itemId, { plaintext: "This should fail" });
    }).toThrow("Cannot update plaintext for item of kind");
  });

  it("should reject filename update for non-file items", () => {
    db = new DB();

    // Insert a message item
    const itemId = "test-message-uuid";
    const itemMetadata = {
      kind: "message" as const,
      uuid: itemId,
      source: "test-source-uuid",
      size: 1024,
      is_read: false,
      seen_by: [],
    };

    db.updateMetadata({
      sources: {},
      items: {
        [itemId]: itemMetadata,
      },
      journalists: {},
    });

    // Try to update filename on a message item - should throw
    expect(() => {
      db.updateItem(itemId, { filename: "this-should-fail.txt" });
    }).toThrow("Cannot update filename for item of kind");
  });

  it("should throw error when database is not initialized", () => {
    db = new DB();
    db.close(); // Close the database

    expect(() => {
      db.updateItem("test-id", { plaintext: "test-content" });
    }).toThrow("Database not initialized");
  });

  it("should throw error when item not found", () => {
    db = new DB();

    expect(() => {
      db.updateItem("nonexistent-id", { plaintext: "test-content" });
    }).toThrow("Item with ID nonexistent-id not found");
  });
});

describe("DB.getUndecryptedMessageIds", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home-undecrypted");
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

  it("should return undecrypted message and reply IDs", () => {
    // Create test metadata with mixed items
    const metadata: MetadataResponse = {
      sources: {
        source1: {
          uuid: "source1",
          journalist_designation: "test source",
          is_starred: false,
          last_updated: "2023-01-01T00:00:00Z",
          public_key: "test-key",
          fingerprint: "test-fingerprint",
        },
      },
      items: {
        message1: {
          kind: "message",
          uuid: "message1",
          source: "source1",
          size: 100,
          is_read: false,
          seen_by: [],
        },
        message2: {
          kind: "message",
          uuid: "message2",
          source: "source1",
          size: 200,
          is_read: false,
          seen_by: [],
        },
        file1: {
          kind: "file",
          uuid: "file1",
          source: "source1",
          size: 300,
          is_read: false,
          seen_by: [],
        },
        reply1: {
          kind: "reply",
          uuid: "reply1",
          source: "source1",
          size: 400,
          journalist_uuid: "journalist1",
          is_deleted_by_source: false,
          seen_by: [],
        },
        reply2: {
          kind: "reply",
          uuid: "reply2",
          source: "source1",
          size: 500,
          journalist_uuid: "journalist2",
          is_deleted_by_source: false,
          seen_by: [],
        },
      },
      journalists: {},
    };

    db.updateMetadata(metadata);

    // Decrypt one message and one reply to test filtering
    db.updateItem("message1", { plaintext: "Decrypted message" });
    db.updateItem("reply1", { plaintext: "Decrypted reply" });

    // Get undecrypted message and reply IDs
    const undecryptedIds = db.getUndecryptedMessageIds();

    // Should return message2 and reply2 (message1 and reply1 are decrypted, file1 is not a message/reply)
    expect(undecryptedIds.sort()).toEqual(["message2", "reply2"]);
  });

  it("should return empty array when all messages are decrypted", () => {
    const metadata: MetadataResponse = {
      sources: {
        source1: {
          uuid: "source1",
          journalist_designation: "test source",
          is_starred: false,
          last_updated: "2023-01-01T00:00:00Z",
          public_key: "test-key",
          fingerprint: "test-fingerprint",
        },
      },
      items: {
        message1: {
          kind: "message",
          uuid: "message1",
          source: "source1",
          size: 100,
          is_read: false,
          seen_by: [],
        },
      },
      journalists: {},
    };

    db.updateMetadata(metadata);
    db.updateItem("message1", { plaintext: "Decrypted content" });

    const undecryptedIds = db.getUndecryptedMessageIds();
    expect(undecryptedIds).toEqual([]);
  });

  it("should throw error when database is not initialized", () => {
    db.close();
    expect(() => db.getUndecryptedMessageIds()).toThrow(
      "Database not initialized",
    );
  });
});

describe("DB.getItems", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home-getitems");
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

  it("should return items by UUIDs", () => {
    // Create a test metadata response with items
    const metadata: MetadataResponse = {
      sources: {
        source1: {
          uuid: "source1",
          journalist_designation: "test source",
          is_starred: false,
          last_updated: "2023-01-01T00:00:00Z",
          public_key: "test-key",
          fingerprint: "test-fingerprint",
        },
      },
      items: {
        item1: {
          kind: "message",
          uuid: "item1",
          source: "source1",
          size: 100,
          is_read: false,
          seen_by: [],
        },
        item2: {
          kind: "file",
          uuid: "item2",
          source: "source1",
          size: 200,
          is_read: true,
          seen_by: ["journalist1"],
        },
      },
      journalists: {},
    };

    db.updateMetadata(metadata);

    // Test getting multiple items
    const items = db.getItems(["item1", "item2"]);
    expect(items).toHaveLength(2);

    const item1 = items.find((item) => item.uuid === "item1");
    const item2 = items.find((item) => item.uuid === "item2");

    expect(item1).toBeDefined();
    expect(item1!.data.kind).toBe("message");
    expect(item1!.plaintext).toBeUndefined();
    expect(item1!.filename).toBeUndefined();

    expect(item2).toBeDefined();
    expect(item2!.data.kind).toBe("file");
    expect(item2!.plaintext).toBeUndefined();
    expect(item2!.filename).toBeUndefined();
  });

  it("should return empty array for empty input", () => {
    const items = db.getItems([]);
    expect(items).toEqual([]);
  });

  it("should throw error when database is not initialized", () => {
    db.close();
    expect(() => db.getItems(["item1"])).toThrow("Database not initialized");
  });
});
