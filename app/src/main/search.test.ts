import { describe, it, expect, beforeEach, afterEach } from "vitest";
import path from "path";
import Database from "better-sqlite3";
import { Search } from "./search";

const nativeBinding = path.join(
  process.cwd(),
  "node_modules",
  "better-sqlite3",
  "build",
  "Release-node",
  "better_sqlite3.node",
);

function createTestDb(): Database.Database {
  const db = new Database(":memory:", { nativeBinding });

  db.exec(`
    CREATE TABLE sources (
      uuid TEXT PRIMARY KEY,
      data JSON,
      version TEXT,
      is_seen INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_seen')) STORED,
      has_attachment INTEGER GENERATED ALWAYS AS (json_extract(data, '$.has_attachment')) STORED
    );

    CREATE TABLE items (
      uuid TEXT PRIMARY KEY,
      data JSON,
      plaintext TEXT,
      filename TEXT,
      version TEXT,
      source_uuid TEXT GENERATED ALWAYS AS (json_extract(data, '$.source')) STORED,
      kind TEXT GENERATED ALWAYS AS (json_extract(data, '$.kind')) STORED,
      is_read INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_read')) STORED,
      last_updated INTEGER GENERATED ALWAYS AS (json_extract(data, '$.last_updated')) STORED,
      fetch_progress INTEGER,
      fetch_status INTEGER NOT NULL DEFAULT 0,
      fetch_last_updated_at TIMESTAMP,
      fetch_retry_attempts INTEGER NOT NULL DEFAULT 0,
      interaction_count INTEGER GENERATED ALWAYS AS (json_extract(data, '$.interaction_count')),
      decrypted_size INTEGER
    );

    CREATE TABLE pending_events (
      snowflake_id TEXT PRIMARY KEY,
      source_uuid TEXT REFERENCES sources(uuid) ON DELETE CASCADE,
      item_uuid TEXT REFERENCES items(uuid) ON DELETE CASCADE,
      type TEXT NOT NULL,
      data JSON,
      CHECK (NOT (source_uuid IS NOT NULL AND item_uuid IS NOT NULL))
    );

    CREATE VIEW sources_projected AS
    WITH latest_starred AS (
      SELECT source_uuid,
        CASE
          WHEN type = 'source_starred' THEN true
          WHEN type = 'source_unstarred' THEN false
        END AS starred_value
      FROM (
        SELECT source_uuid, type,
          ROW_NUMBER() OVER (PARTITION BY source_uuid ORDER BY snowflake_id DESC) AS rn
        FROM pending_events
        WHERE type IN ('source_starred', 'source_unstarred') AND source_uuid IS NOT NULL
      ) latest
      WHERE rn = 1
    )
    SELECT
      sources.uuid,
      CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set(sources.data, '$.is_starred', starred_value)
        ELSE sources.data
      END AS data,
      sources.version,
      sources.has_attachment,
      CASE
        WHEN EXISTS (
          SELECT 1 FROM pending_events
          WHERE pending_events.source_uuid = sources.uuid AND pending_events.type = 'item_seen'
        ) THEN 1
        ELSE sources.is_seen
      END AS is_seen
    FROM sources
    LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
    WHERE NOT EXISTS (
      SELECT 1 FROM pending_events
      WHERE pending_events.source_uuid = sources.uuid AND pending_events.type = 'source_deleted'
    );

    CREATE VIEW items_projected AS
    SELECT
      items.uuid, items.data, items.version, items.plaintext, items.filename,
      items.kind, items.is_read, items.last_updated, items.source_uuid,
      items.fetch_progress, items.fetch_status, items.fetch_last_updated_at,
      items.fetch_retry_attempts, items.interaction_count, items.decrypted_size
    FROM items
    WHERE NOT EXISTS (
      SELECT 1 FROM pending_events
      WHERE pending_events.item_uuid = items.uuid AND pending_events.type = 'item_deleted'
    ) AND NOT EXISTS (
      SELECT 1 FROM pending_events
      WHERE pending_events.source_uuid = items.source_uuid
        AND pending_events.type IN ('source_deleted', 'source_conversation_deleted')
    )
    UNION ALL
    SELECT
      json_extract(pending_events.data, '$.metadata.uuid') AS uuid,
      json_extract(pending_events.data, '$.metadata') AS data,
      NULL AS version,
      json_extract(pending_events.data, '$.plaintext') AS plaintext,
      NULL AS filename, 'reply' AS kind, NULL AS is_read, NULL AS last_updated,
      json_extract(pending_events.data, '$.metadata.source') AS source_uuid,
      NULL AS fetch_progress, NULL AS fetch_status, NULL AS fetch_last_updated_at,
      NULL AS fetch_retry_attempts,
      json_extract(pending_events.data, '$.metadata.interaction_count') AS interaction_count,
      NULL AS decrypted_size
    FROM pending_events
    WHERE pending_events.type = 'reply_sent'
      AND NOT EXISTS (
        SELECT 1 FROM pending_events later
        WHERE (
          (later.source_uuid = json_extract(pending_events.data, '$.metadata.source')
            AND later.type IN ('source_deleted', 'source_conversation_deleted'))
          OR (later.item_uuid = json_extract(pending_events.data, '$.metadata.uuid')
            AND later.type = 'item_deleted')
        ) AND later.snowflake_id > pending_events.snowflake_id
      );

    CREATE VIRTUAL TABLE search_index USING fts5(
      source_uuid UNINDEXED,
      item_uuid UNINDEXED,
      type UNINDEXED,
      content,
      tokenize='unicode61'
    );
  `);

  return db;
}

function insertSource(
  db: Database.Database,
  uuid: string,
  designation: string,
) {
  db.prepare("INSERT INTO sources (uuid, data) VALUES (?, ?)").run(
    uuid,
    JSON.stringify({
      journalist_designation: designation,
      is_seen: true,
      is_starred: false,
      has_attachment: false,
    }),
  );
}

function insertItem(
  db: Database.Database,
  uuid: string,
  sourceUuid: string,
  kind: "message" | "reply" | "file",
  opts: { plaintext?: string; filename?: string } = {},
) {
  db.prepare(
    "INSERT INTO items (uuid, data, plaintext, filename) VALUES (?, ?, ?, ?)",
  ).run(
    uuid,
    JSON.stringify({
      source: sourceUuid,
      kind,
      is_read: false,
      last_updated: Date.now(),
      interaction_count: 1,
    }),
    opts.plaintext ?? null,
    opts.filename ?? null,
  );
}

describe("Search", () => {
  let db: Database.Database;
  let search: Search;

  beforeEach(() => {
    db = createTestDb();
    search = new Search(db);
  });

  afterEach(() => {
    db.close();
  });

  describe("search", () => {
    it("returns empty array for empty query", () => {
      expect(search.search("")).toEqual([]);
      expect(search.search("   ")).toEqual([]);
    });

    it("returns empty array for query with only special characters", () => {
      expect(search.search("'\"*()")).toEqual([]);
    });

    it("finds a source by journalist designation", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      search.indexSource("source-1");

      const results = search.search("colorful");
      expect(results).toHaveLength(1);
      expect(results[0]).toEqual({
        sourceUuid: "source-1",
        itemUuid: null,
        snippet: expect.stringContaining("colorful"),
        type: "source",
      });
    });

    it("finds a message by plaintext content", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "hello world secret document",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      const results = search.search("secret");
      expect(results).toHaveLength(1);
      expect(results[0]).toEqual({
        sourceUuid: "source-1",
        itemUuid: "item-1",
        snippet: expect.stringContaining("secret"),
        type: "message",
      });
    });

    it("finds a file by filename", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "file", {
        filename: "budget-report.pdf",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      const results = search.search("budget");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("file");
      expect(results[0].itemUuid).toBe("item-1");
    });

    it("finds a reply by plaintext", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "reply", {
        plaintext: "thanks for the tip",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      const results = search.search("tip");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("reply");
    });

    it("returns multiple results across sources and items", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertSource(db, "source-2", "dramatic dolphin");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "colorful flowers in the garden",
      });
      search.indexSource("source-1");
      search.indexSource("source-2");
      search.indexItem("item-1");

      const results = search.search("colorful");
      expect(results).toHaveLength(2);
      const types = results.map((r) => r.type);
      expect(types).toContain("source");
      expect(types).toContain("message");
    });

    it("supports prefix matching", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      search.indexSource("source-1");

      const results = search.search("cater");
      expect(results).toHaveLength(1);
      expect(results[0].snippet).toEqual(
        expect.stringContaining("caterpillar"),
      );
    });

    it("sanitizes special FTS5 characters in query", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "hello world",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      // These should not throw
      expect(() => search.search('"hello"')).not.toThrow();
      expect(() => search.search("hello*world")).not.toThrow();
      expect(() => search.search("(hello)")).not.toThrow();
      expect(() => search.search("it's")).not.toThrow();

      const results = search.search('"hello"');
      expect(results).toHaveLength(1);
    });

    it("does not return results for deleted sources", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      search.indexSource("source-1");

      // Mark source as deleted via pending event
      db.prepare(
        "INSERT INTO pending_events (snowflake_id, source_uuid, type) VALUES (?, ?, ?)",
      ).run("1", "source-1", "source_deleted");

      const results = search.search("colorful");
      expect(results).toHaveLength(0);
    });

    it("does not return results after removeItem is called", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "secret document",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      search.removeItem("item-1");

      const results = search.search("secret");
      expect(results).toHaveLength(0);
    });
  });

  describe("indexItem", () => {
    it("indexes an item with plaintext", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "sensitive information",
      });

      search.indexItem("item-1");

      const results = search.search("sensitive");
      expect(results).toHaveLength(1);
      expect(results[0].itemUuid).toBe("item-1");
      expect(results[0].type).toBe("message");
    });

    it("indexes an item with filename", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "file", {
        filename: "evidence.zip",
      });

      search.indexItem("item-1");

      const results = search.search("evidence");
      expect(results).toHaveLength(1);
      expect(results[0].type).toBe("file");
    });

    it("prefers plaintext over filename", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "the real content",
        filename: "original.txt",
      });

      search.indexItem("item-1");

      const results = search.search("real content");
      expect(results).toHaveLength(1);

      // filename should not be separately indexed
      const filenameResults = search.search("original");
      expect(filenameResults).toHaveLength(0);
    });

    it("skips items with no plaintext or filename", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message");

      search.indexItem("item-1");

      // Only the source should be findable, not the item
      const allRows = db
        .prepare("SELECT * FROM search_index WHERE item_uuid = ?")
        .all("item-1");
      expect(allRows).toHaveLength(0);
    });

    it("skips nonexistent items", () => {
      search.indexItem("nonexistent");
      const allRows = db.prepare("SELECT * FROM search_index").all();
      expect(allRows).toHaveLength(0);
    });

    it("replaces existing entry on re-index", () => {
      insertSource(db, "source-1", "colorful caterpillar");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "old content",
      });
      search.indexItem("item-1");

      // Update the plaintext
      db.prepare("UPDATE items SET plaintext = ? WHERE uuid = ?").run(
        "new content",
        "item-1",
      );
      search.indexItem("item-1");

      expect(search.search("old")).toHaveLength(0);
      expect(search.search("new content")).toHaveLength(1);
    });
  });

  describe("indexSource", () => {
    it("indexes a source by journalist designation", () => {
      insertSource(db, "source-1", "dramatic dolphin");

      search.indexSource("source-1");

      const results = search.search("dramatic");
      expect(results).toHaveLength(1);
      expect(results[0]).toMatchObject({
        sourceUuid: "source-1",
        itemUuid: null,
        type: "source",
      });
    });

    it("updates source name on re-index", () => {
      insertSource(db, "source-1", "old name");
      search.indexSource("source-1");

      // Update source designation
      db.prepare("UPDATE sources SET data = ? WHERE uuid = ?").run(
        JSON.stringify({
          journalist_designation: "new name",
          is_seen: true,
          is_starred: false,
          has_attachment: false,
        }),
        "source-1",
      );
      search.indexSource("source-1");

      expect(search.search("old")).toHaveLength(0);
      expect(search.search("new name")).toHaveLength(1);
    });

    it("does not duplicate source rows on re-index", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      search.indexSource("source-1");
      search.indexSource("source-1");
      search.indexSource("source-1");

      const results = search.search("dramatic");
      expect(results).toHaveLength(1);
    });

    it("skips nonexistent sources", () => {
      search.indexSource("nonexistent");
      const allRows = db.prepare("SELECT * FROM search_index").all();
      expect(allRows).toHaveLength(0);
    });

    it("does not affect item rows for the same source", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "secret message",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      // Re-index source should not remove the item row
      search.indexSource("source-1");

      expect(search.search("secret")).toHaveLength(1);
      expect(search.search("dramatic")).toHaveLength(1);
    });
  });

  describe("removeSource", () => {
    it("removes all entries for a source", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "secret info",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      search.removeSource("source-1");

      expect(search.search("dramatic")).toHaveLength(0);
      expect(search.search("secret")).toHaveLength(0);
    });

    it("does not affect other sources", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      insertSource(db, "source-2", "elegant elephant");
      search.indexSource("source-1");
      search.indexSource("source-2");

      search.removeSource("source-1");

      expect(search.search("dramatic")).toHaveLength(0);
      expect(search.search("elegant")).toHaveLength(1);
    });
  });

  describe("removeItem", () => {
    it("removes a specific item entry", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "secret info",
      });
      search.indexSource("source-1");
      search.indexItem("item-1");

      search.removeItem("item-1");

      expect(search.search("secret")).toHaveLength(0);
      // Source entry should remain
      expect(search.search("dramatic")).toHaveLength(1);
    });

    it("does not affect other items", () => {
      insertSource(db, "source-1", "dramatic dolphin");
      insertItem(db, "item-1", "source-1", "message", {
        plaintext: "first message",
      });
      insertItem(db, "item-2", "source-1", "message", {
        plaintext: "second message",
      });
      search.indexItem("item-1");
      search.indexItem("item-2");

      search.removeItem("item-1");

      expect(search.search("first")).toHaveLength(0);
      expect(search.search("second")).toHaveLength(1);
    });
  });
});
