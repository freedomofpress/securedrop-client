import { describe, it, expect, beforeEach, afterEach } from "vitest";
import path from "path";
import fs from "fs";
import os from "os";
import { Datastore } from "../datastore";
import { buildQuery } from "./search";
import { Crypto } from "../crypto";
import { Storage } from "../storage";
import { PendingEventType } from "../../types";
import type { SourceMetadata, ItemMetadata } from "../../types";

function mockSource(uuid: string, designation: string): SourceMetadata {
  return {
    uuid,
    journalist_designation: designation,
    is_starred: false,
    is_seen: true,
    has_attachment: false,
    last_updated: "2024-01-01T00:00:00Z",
    public_key: "test-public-key",
    fingerprint: "ABCD1234",
  };
}

function mockItem(
  uuid: string,
  sourceUuid: string,
  kind: "message" | "reply" | "file",
): ItemMetadata {
  if (kind === "reply") {
    return {
      kind: "reply",
      uuid,
      source: sourceUuid,
      size: 0,
      journalist_uuid: "journalist",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: 1,
    };
  }
  return {
    kind,
    uuid,
    source: sourceUuid,
    size: 0,
    is_read: false,
    seen_by: [],
    interaction_count: 1,
  };
}

describe("buildQuery", () => {
  it("returns null for empty string", () => {
    expect(buildQuery("")).toBeNull();
  });

  it("returns null for whitespace-only input", () => {
    expect(buildQuery("   ")).toBeNull();
  });

  it("returns null for input with only special characters", () => {
    expect(buildQuery("'\"*()")).toBeNull();
  });

  it("wraps a single term with quotes and a prefix wildcard", () => {
    expect(buildQuery("hello")).toBe('"hello"*');
  });

  it("wraps multiple unquoted terms individually", () => {
    expect(buildQuery("hello world")).toBe('"hello"* "world"*');
  });

  it("normalizes extra whitespace between unquoted terms", () => {
    expect(buildQuery("  hello   world  ")).toBe('"hello"* "world"*');
  });

  it("keeps a quoted phrase as a single term with a prefix wildcard", () => {
    expect(buildQuery('"hello world"')).toBe('"hello world"*');
  });

  it("handles multiple quoted phrases", () => {
    expect(buildQuery('"hello bob" "goodbye alice"')).toBe(
      '"hello bob"* "goodbye alice"*',
    );
  });

  it("handles quoted phrases mixed with unquoted terms", () => {
    expect(buildQuery('"hello world" secret')).toBe('"hello world"* "secret"*');
    expect(buildQuery('secret "hello world"')).toBe('"secret"* "hello world"*');
    expect(buildQuery('before "mid dle" after')).toBe(
      '"before"* "mid dle"* "after"*',
    );
  });

  it("treats an unclosed quote as a phrase", () => {
    expect(buildQuery('"hello world')).toBe('"hello world"*');
    expect(buildQuery('start "unclosed')).toBe('"start"* "unclosed"*');
  });

  it("skips empty quoted phrases", () => {
    expect(buildQuery('""')).toBeNull();
    expect(buildQuery('"" hello')).toBe('"hello"*');
    expect(buildQuery('hello ""')).toBe('"hello"*');
  });

  it("sanitizes * in unquoted text", () => {
    expect(buildQuery("hello*world")).toBe('"hello"* "world"*');
  });

  it("sanitizes parentheses in unquoted text", () => {
    expect(buildQuery("(hello)")).toBe('"hello"*');
    expect(buildQuery("hello(world)")).toBe('"hello"* "world"*');
  });

  it("sanitizes apostrophes in unquoted text by splitting on them", () => {
    // ' is replaced with a space, so "it's" becomes two tokens
    expect(buildQuery("it's")).toBe('"it"* "s"*');
  });

  it("sanitizes special chars inside a quoted phrase", () => {
    // * inside quotes becomes a space; the phrase is still kept together
    expect(buildQuery('"hello*world"')).toBe('"hello world"*');
    // () inside quotes become spaces and are trimmed away
    expect(buildQuery('"(parenthesized)"')).toBe('"parenthesized"*');
  });
});

describe("Search", () => {
  let db: Datastore;
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "sd-search-test-"));
    db = new Datastore({} as Crypto, new Storage(), tmpDir);
  });

  afterEach(() => {
    db.close();
    fs.rmSync(tmpDir, { recursive: true });
  });

  describe("search", () => {
    it("returns empty array for empty query", () => {
      expect(db.search("")).toEqual([]);
      expect(db.search("   ")).toEqual([]);
    });

    it("returns empty array for query with only special characters", () => {
      expect(db.search("'\"*()")).toEqual([]);
    });

    it("finds a source by journalist designation", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });

      const results = db.search("colorful");
      expect(results).toHaveLength(1);
      expect(results[0]).toEqual({
        sourceUuid: "source1",
        itemUuid: null,
        snippet: expect.stringContaining("colorful"),
        type: "source",
      });
    });

    it("finds a message by plaintext content", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem(
        "item1",
        "hello world secret document",
        false,
        null,
      );

      const results = db.search("secret");
      expect(results).toHaveLength(1);
      expect(results[0]).toEqual({
        sourceUuid: "source1",
        itemUuid: "item1",
        snippet: expect.stringContaining("secret"),
        type: "message",
      });
    });

    it("finds a file by filename", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "file") });
      db.completeFileItem("item1", "budget-report.pdf", 1000, false, null);

      const results = db.search("budget");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("file");
      expect(results[0].itemUuid).toBe("item1");
    });

    it("finds a reply by plaintext", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "reply") });
      db.completePlaintextItem("item1", "thanks for the tip", false, null);

      const results = db.search("tip");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("reply");
    });

    it("returns one result per source when multiple items match", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem(
        "item1",
        "colorful flowers in the garden",
        false,
        null,
      );

      // Both the source name and the message match, but we expect only one
      // result for source1 (the highest-ranked row).
      const results = db.search("colorful");
      expect(results).toHaveLength(1);
      expect(results[0].sourceUuid).toBe("source1");
    });

    it("returns one result per matching source", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
        ["source2"]: mockSource("source2", "colorful dolphin"),
      });

      const results = db.search("colorful");
      expect(results).toHaveLength(2);
      const sourceUuids = results.map((r) => r.sourceUuid);
      expect(sourceUuids).toContain("source1");
      expect(sourceUuids).toContain("source2");
    });

    it("supports prefix matching", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });

      const results = db.search("cater");
      expect(results).toHaveLength(1);
      expect(results[0].snippet).toEqual(
        expect.stringContaining("caterpillar"),
      );
    });

    it("sanitizes special characters in query", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "hello world", false, null);

      // These should not throw
      expect(() => db.search('"hello"')).not.toThrow();
      expect(() => db.search("hello*world")).not.toThrow();
      expect(() => db.search("(hello)")).not.toThrow();
      expect(() => db.search("it's")).not.toThrow();

      const results = db.search('"hello"');
      expect(results).toHaveLength(1);
    });

    it("does not return results for deleted sources", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.addPendingSourceEvent("source1", PendingEventType.SourceDeleted);

      const results = db.search("colorful");
      expect(results).toHaveLength(0);
    });

    it("does not return results for deleted items", async () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret document", false, null);

      await db.deleteItemsAsync(["item1"]);

      const results = db.search("secret");
      expect(results).toHaveLength(0);
    });

    it("does not return item results pending deletion via item_deleted event", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret document", false, null);

      db.addPendingItemEvent("item1", PendingEventType.ItemDeleted);

      const results = db.search("secret");
      expect(results).toHaveLength(0);
    });

    it("does not return item results pending deletion via source_conversation_truncated event", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret document", false, null);

      db.addPendingSourceEvent(
        "source1",
        PendingEventType.SourceConversationTruncated,
        { upper_bound: 1 },
      );

      const results = db.search("secret");
      expect(results).toHaveLength(0);
    });

    it("still returns source result when item is pending deletion", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret document", false, null);

      db.addPendingItemEvent("item1", PendingEventType.ItemDeleted);

      const results = db.search("colorful");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("source");
    });
  });

  describe("indexItem", () => {
    it("indexes an item with plaintext", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "sensitive information", false, null);

      const results = db.search("sensitive");
      expect(results).toHaveLength(1);
      expect(results[0].itemUuid).toBe("item1");
      expect(results[0].type).toBe("message");
    });

    it("indexes an item with filename", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "file") });
      db.completeFileItem("item1", "evidence.zip", 500, false, null);

      const results = db.search("evidence");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("file");
    });

    it("prefers plaintext over filename", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      // Set filename first, then plaintext — plaintext should win in the index
      db.completeFileItem("item1", "original.txt", 100, false, null);
      db.completePlaintextItem("item1", "the real content", false, null);

      const results = db.search("real content");
      expect(results).toHaveLength(1);

      // filename should no longer be indexed
      const filenameResults = db.search("original");
      expect(filenameResults).toHaveLength(0);
    });

    it("skips items with no plaintext or filename", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      // completePlaintextItem is never called, so the item is never indexed

      // Source is findable; item is not (it has no content in the index)
      expect(db.search("caterpillar")).toHaveLength(1); // source only
      expect(db.search("caterpillar")[0].type).toBe("source");
    });

    it("replaces existing entry on re-index", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "colorful caterpillar"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "old content", false, null);
      db.completePlaintextItem("item1", "new content", false, null);

      expect(db.search("old")).toHaveLength(0);
      expect(db.search("new content")).toHaveLength(1);
    });
  });

  describe("indexSource", () => {
    it("indexes a source by journalist designation", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });

      const results = db.search("dramatic");
      expect(results).toHaveLength(1);
      expect(results[0]).toMatchObject({
        sourceUuid: "source1",
        itemUuid: null,
        type: "source",
      });
    });

    it("updates source name on re-index", () => {
      db.updateSources({ ["source1"]: mockSource("source1", "old name") });
      db.updateSources({ ["source1"]: mockSource("source1", "new name") });

      expect(db.search("old")).toHaveLength(0);
      expect(db.search("new name")).toHaveLength(1);
    });

    it("does not duplicate source rows on re-index", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });

      const results = db.search("dramatic");
      expect(results).toHaveLength(1);
    });

    it("does not affect item rows for the same source", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret message", false, null);

      // Re-indexing the source should not remove the item row
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });

      expect(db.search("secret")).toHaveLength(1);
      expect(db.search("dramatic")).toHaveLength(1);
    });
  });

  describe("deleteSources", () => {
    it("removes all entries for a source", async () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret info", false, null);

      await db.deleteSourcesAsync(["source1"]);

      expect(db.search("dramatic")).toHaveLength(0);
      expect(db.search("secret")).toHaveLength(0);
    });

    it("does not affect other sources", async () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
        ["source2"]: mockSource("source2", "elegant elephant"),
      });

      await db.deleteSourcesAsync(["source1"]);

      expect(db.search("dramatic")).toHaveLength(0);
      expect(db.search("elegant")).toHaveLength(1);
    });
  });

  describe("deleteItems", () => {
    it("removes a specific item entry", async () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "secret info", false, null);

      await db.deleteItemsAsync(["item1"]);

      expect(db.search("secret")).toHaveLength(0);
      // Source entry should remain
      expect(db.search("dramatic")).toHaveLength(1);
    });

    it("does not affect other items", async () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateItems({
        ["item1"]: mockItem("item1", "source1", "message"),
        ["item2"]: mockItem("item2", "source1", "message"),
      });
      db.completePlaintextItem("item1", "first message", false, null);
      db.completePlaintextItem("item2", "second message", false, null);

      await db.deleteItemsAsync(["item1"]);

      expect(db.search("first")).toHaveLength(0);
      expect(db.search("second")).toHaveLength(1);
    });
  });

  describe("update from sync", () => {
    it("removes from search index on updateItems call", () => {
      db.updateSources({
        ["source1"]: mockSource("source1", "dramatic dolphin"),
      });
      db.updateItems({ ["item1"]: mockItem("item1", "source1", "message") });
      db.completePlaintextItem("item1", "classified content", false, null);

      // Verify the item is indexed before deletion
      expect(db.search("classified")).toHaveLength(1);

      db.updateItems({ ["item1"]: null });

      expect(db.search("classified")).toHaveLength(0);
      // Source entry should still be findable
      expect(db.search("dramatic")).toHaveLength(1);
    });
  });
});
