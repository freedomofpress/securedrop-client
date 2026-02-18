import Database, { Statement } from "better-sqlite3";
import { SearchResult } from "../../types";

type SearchRow = {
  source_uuid: string;
  item_uuid: string | null;
  type: "message" | "reply" | "file" | "source";
  snippet: string | null;
};

type IndexItemRow = {
  source_uuid: string;
  kind: "message" | "reply" | "file";
  plaintext: string | null;
  filename: string | null;
};

type IndexSourceRow = {
  source_name: string;
};

export class Search {
  private db: Database.Database;

  private searchStmt: Statement<[string, number, number], SearchRow>;
  private deleteByItemStmt: Statement<[string], void>;
  private deleteBySourceStmt: Statement<[string], void>;
  private upsertItemStmt: Statement<
    {
      source_uuid: string;
      item_uuid: string;
      type: string;
      content: string;
    },
    void
  >;
  private upsertSourceStmt: Statement<
    {
      source_uuid: string;
      content: string;
    },
    void
  >;
  private selectItemStmt: Statement<[string], IndexItemRow>;
  private selectSourceStmt: Statement<[string], IndexSourceRow>;

  constructor(db: Database.Database) {
    this.db = db;

    this.searchStmt = this.db.prepare(`
      SELECT
        si.source_uuid,
        si.item_uuid,
        si.type,
        content AS snippet
      FROM search_index si
      INNER JOIN sources_projected sp ON sp.uuid = si.source_uuid
      LEFT JOIN items_projected ip ON ip.uuid = si.item_uuid
      WHERE search_index MATCH ?
      ORDER BY rank
      LIMIT ? OFFSET ?
    `);

    this.deleteByItemStmt = this.db.prepare(
      `DELETE FROM search_index WHERE item_uuid = ?`,
    );

    this.deleteBySourceStmt = this.db.prepare(
      `DELETE FROM search_index WHERE source_uuid = ?`,
    );

    this.upsertItemStmt = this.db.prepare(`
      INSERT OR REPLACE INTO search_index(rowid, source_uuid, item_uuid, type, content)
      VALUES (
        (SELECT rowid FROM search_index WHERE item_uuid = @item_uuid),
        @source_uuid, @item_uuid, @type, @content
      )
    `);

    this.upsertSourceStmt = this.db.prepare(`
      INSERT OR REPLACE INTO search_index(rowid, source_uuid, item_uuid, type, content)
      VALUES (
        (SELECT rowid FROM search_index WHERE source_uuid = @source_uuid AND type = 'source'),
        @source_uuid, NULL, 'source', @content
      )
    `);

    this.selectItemStmt = this.db.prepare(`
      SELECT i.source_uuid,
             json_extract(i.data, '$.kind') AS kind,
             i.plaintext, i.filename
      FROM items i
      WHERE i.uuid = ?
    `);

    this.selectSourceStmt = this.db.prepare(`
      SELECT json_extract(data, '$.journalist_designation') AS source_name
      FROM sources WHERE uuid = ?
    `);
  }

  search(
    query: string,
    limit: number = 20,
    offset: number = 0,
  ): SearchResult[] {
    if (!query.trim()) {
      return [];
    }

    // Escape special FTS5 characters and append * for prefix matching
    const sanitized = query.replace(/['"*()]/g, " ").trim();
    if (!sanitized) {
      return [];
    }

    const ftsQuery = sanitized
      .split(/\s+/)
      .map((term) => `"${term}"*`)
      .join(" ");

    const rows = this.searchStmt.all(ftsQuery, limit, offset);
    return rows.map((row) => ({
      sourceUuid: row.source_uuid,
      itemUuid: row.item_uuid,
      snippet: row.snippet,
      type: row.type,
    }));
  }

  indexItem(itemUuid: string): void {
    const row = this.selectItemStmt.get(itemUuid);
    if (!row) return;

    const content = row.plaintext ?? row.filename;
    if (!content) return;

    this.upsertItemStmt.run({
      source_uuid: row.source_uuid,
      item_uuid: itemUuid,
      type: row.kind,
      content,
    });
  }

  indexSource(sourceUuid: string): void {
    const row = this.selectSourceStmt.get(sourceUuid);
    if (!row) return;

    this.upsertSourceStmt.run({
      source_uuid: sourceUuid,
      content: row.source_name,
    });
  }

  removeSource(sourceUuid: string): void {
    this.deleteBySourceStmt.run(sourceUuid);
  }

  removeItem(itemUuid: string): void {
    this.deleteByItemStmt.run(itemUuid);
  }

  close(): void {
    this.db?.close();
  }
}
