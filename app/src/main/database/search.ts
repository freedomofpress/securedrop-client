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

/**
 * Build an FTS5 query from a user-supplied search string.
 *
 * - Quoted substrings (e.g. `"hello world"`) are kept together as a phrase
 *   and matched with a trailing prefix wildcard: `"hello world"*`
 * - Unquoted tokens are split and prefix matched: `"hello"* "world"*`
 * - An unclosed opening quote is treated as a phrase until end of input
 * - Special query characters (`'`, `"`, `*`, `(`, `)`) are sanitized to prevent query injection
 */
export function buildQuery(input: string): string | null {
  const trimmed = input.trim();
  if (!trimmed) {
    return null;
  }

  const terms: string[] = [];
  let i = 0;

  while (i < trimmed.length) {
    if (trimmed[i] === '"') {
      // Quoted phrase: find the closing quote
      const close = trimmed.indexOf('"', i + 1);
      let phraseContent: string;

      if (close === -1) {
        // Unclosed quote — treat the rest of the string as a phrase
        phraseContent = trimmed.slice(i + 1);
        i = trimmed.length;
      } else {
        phraseContent = trimmed.slice(i + 1, close);
        i = close + 1;
      }
      const sanitized = phraseContent.replace(/['"*()]/g, " ").trim();
      if (sanitized) {
        terms.push(`"${sanitized}"*`);
      }
    } else {
      // Unquoted section: collect up to the next quote (or end of string)
      const nextQuote = trimmed.indexOf('"', i);
      const chunk =
        nextQuote === -1 ? trimmed.slice(i) : trimmed.slice(i, nextQuote);
      i = nextQuote === -1 ? trimmed.length : nextQuote;

      // Replace special chars with spaces, then split into tokens
      chunk
        .replace(/['*()]/g, " ")
        .split(/\s+/)
        .filter(Boolean)
        .forEach((token) => terms.push(`"${token}"*`));
    }
  }

  return terms.length > 0 ? terms.join(" ") : null;
}

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
    const ftsQuery = buildQuery(query);
    if (!ftsQuery) {
      return [];
    }

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
    if (!row) {
      return;
    }

    // Index either message plaintext or filename without path
    const content =
      row.plaintext ??
      row.filename?.substring(row.filename.lastIndexOf("/") + 1);
    if (!content) {
      return;
    }

    this.upsertItemStmt.run({
      source_uuid: row.source_uuid,
      item_uuid: itemUuid,
      type: row.kind,
      content,
    });
  }

  indexSource(sourceUuid: string): void {
    const row = this.selectSourceStmt.get(sourceUuid);
    if (!row) {
      return;
    }

    this.upsertSourceStmt.run({
      source_uuid: sourceUuid,
      content: row.source_name,
    });
  }

  // Removes source and all its items from the search index
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
