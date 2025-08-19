import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database, { Statement } from "better-sqlite3";
import blake from "blakejs";

import type {
  Index,
  SourceMetadata,
  ItemMetadata,
  MetadataResponse,
  Source,
  SourceWithItems,
  SourceRow,
  ItemRow,
} from "../../types";

const sortKeys = (_, value) =>
  value instanceof Object && !(value instanceof Array)
    ? Object.keys(value)
        .sort()
        .reduce((sorted, key) => {
          sorted[key] = value[key];
          return sorted;
        }, {})
    : value;

// Calculate the version (BLAKE2s digest) of the normalized JSON representation
// of the provided JSON object.
//
// This matches the SecureDrop server implementation of the version calculation.
// We use BLAKE2s because it is faster than SHA256 and we don't need cryptographic
// security, and CRC32 is too collision-prone.
function computeVersion(blob: string): string {
  return blake.blake2sHex(blob);
}

export class DB {
  private db: Database.Database | null;
  private url: string | null;

  // Prepared statements
  private selectVersion: Statement<[], { version: string }>;
  private insertVersion: Statement<[string], void>;

  private selectAllSourceVersion: Statement<
    [],
    { uuid: string; version: string }
  >;
  private upsertSource: Statement<
    { id: string; data: string; version: string },
    void
  >;
  private deleteSource: Statement<{ id: string }, void>;

  private selectAllItemVersion: Statement<
    [],
    { uuid: string; version: string }
  >;
  private upsertItem: Statement<
    { id: string; data: string; version: string },
    void
  >;
  private deleteItem: Statement<{ id: string }, void>;

  constructor() {
    // Ensure the directory exists
    const dbDir = path.join(os.homedir(), ".config", "SecureDrop");
    if (!fs.existsSync(dbDir)) {
      fs.mkdirSync(dbDir, { recursive: true });
    }

    // Create or open the SQLite database
    const dbPath = path.join(dbDir, "db.sqlite");
    const db = new Database(dbPath, {});
    db.pragma("journal_mode = WAL");

    // Set the database URL for migrations
    this.url = `sqlite:${dbPath}`;
    this.db = db;

    // Run migrations (before we prepare any statements based on the latest schema)
    this.runMigrations();

    // Prepare statements
    this.selectVersion = this.db.prepare("SELECT version FROM state");
    this.insertVersion = this.db.prepare(
      "INSERT INTO state_history (version) VALUES (?)",
    );

    this.selectAllSourceVersion = this.db.prepare(
      "SELECT uuid, version FROM sources",
    );
    this.upsertSource = this.db.prepare(
      "INSERT INTO sources (uuid, data, version) VALUES (@id, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteSource = this.db.prepare("DELETE FROM sources WHERE uuid = @id");

    this.selectAllItemVersion = this.db.prepare(
      "SELECT uuid, version FROM items",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@id, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteItem = this.db.prepare("DELETE FROM items WHERE uuid = @id");
  }

  runMigrations(): void {
    if (!this.url) {
      throw new Error(
        "Database URL is not set. Ensure the database is opened first.",
      );
    }

    // Determine if we're in a packaged app or development
    const isPackaged = __dirname.includes("app.asar");

    let dbmatePath: string;
    let migrationsDir: string;

    if (isPackaged) {
      // For packaged apps, binaries and migrations are outside the asar archive
      dbmatePath = path.join(process.resourcesPath, "bin", "dbmate");
      migrationsDir = path.join(process.resourcesPath, "migrations");
    } else {
      // In development, use paths relative to current working directory
      dbmatePath = path.join(process.cwd(), "node_modules", ".bin", "dbmate");
      migrationsDir = path.join(
        process.cwd(),
        "src",
        "main",
        "database",
        "migrations",
      );
    }

    // Ensure migrations directory exists
    if (!fs.existsSync(migrationsDir)) {
      throw new Error(`Migrations directory not found: ${migrationsDir}`);
    }

    // Ensure dbmate binary exists
    if (!fs.existsSync(dbmatePath)) {
      throw new Error(`dbmate binary not found: ${dbmatePath}`);
    }

    try {
      const command = [
        `"${dbmatePath}"`,
        `--url "${this.url}"`,
        `--migrations-dir "${migrationsDir}"`,
        // Don't update the schema file when running migrations at app startup
        `--schema-file "/dev/null"`,
        "up",
      ].join(" ");

      console.log("Running migrations:", command);
      execSync(command, { stdio: "inherit" });
      console.log("Migrations completed successfully");
    } catch (error) {
      console.error("Migration failed:", error);
      throw new Error(`Migration failed: ${error}`);
    }
  }

  close(): void {
    this.db?.close();
    this.db = null;
    this.url = null;
  }

  /// Read the current index version from the DB for sync.
  /// If we are in the initial sync state and there is no
  // source data available, then we return empty.
  getVersion(): string {
    const version = this.selectVersion.get();
    if (!version) {
      return "";
    }
    return version.version;
  }

  getIndex(): Index {
    // NOTE: setting journalists to empty object for now, as implementing
    // journalist sync is still TODO.
    const index = { sources: {}, items: {}, journalists: {} };
    for (const row of this.selectAllSourceVersion.iterate()) {
      index.sources[row.uuid] = row.version;
    }
    for (const row of this.selectAllItemVersion.iterate()) {
      index.items[row.uuid] = row.version;
    }
    return index;
  }

  // Updates the index version: should be called on any write operation to
  // sources or items
  private updateVersion() {
    const index = this.getIndex();
    const strIndex = JSON.stringify(index, sortKeys);
    const newVersion = computeVersion(strIndex);
    this.insertVersion.run(newVersion);
  }

  deleteItems(items: string[]) {
    this.db!.transaction((items) => {
      for (const itemID in items) {
        this.deleteItem.run({ id: itemID });
      }
      this.updateVersion();
    })(items);
  }

  deleteSources(sources: string[]) {
    this.db!.transaction((sources) => {
      for (const sourceID in sources) {
        this.deleteSource.run({ id: sourceID });
      }
      this.updateVersion();
    })(sources);
  }

  updateMetadata(metadata: MetadataResponse) {
    this.db!.transaction((metadata: MetadataResponse) => {
      this.updateSources(metadata.sources);
      this.updateItems(metadata.items);
      this.updateVersion();
    })(metadata);
  }

  // Updates source versions in DB. Should be run in a transaction that also
  // updates the global index version.
  private updateSources(sources: { [uuid: string]: SourceMetadata }) {
    Object.keys(sources).forEach((sourceid: string) => {
      const metadata = sources[sourceid];
      // Updating the full source: update metadata and re-compute source version
      const info = JSON.stringify(metadata, sortKeys);
      const version = computeVersion(info);
      this.upsertSource.run({
        id: sourceid,
        data: info,
        version: version,
      });
    });
  }

  // Updates item versions in DB. Should be run in a transaction that also
  // updates the global index version.
  private updateItems(items: { [uuid: string]: ItemMetadata }) {
    Object.keys(items).forEach((itemid: string) => {
      const metadata = items[itemid];
      const blob = JSON.stringify(metadata, sortKeys);
      const version = computeVersion(blob);
      this.upsertItem.run({
        id: itemid,
        data: blob,
        version: version,
      });
    });
  }

  // Helper function for truthy values
  private isTruthy(value: unknown): boolean {
    if (typeof value === "boolean") return value;
    if (typeof value === "number") return value !== 0;
    if (typeof value === "string")
      return value.toLowerCase() === "true" || value === "1";
    return Boolean(value);
  }

  getSources(params?: {
    searchTerm?: string;
    filter?: "all" | "read" | "unread" | "starred" | "unstarred";
    sortedAsc?: boolean;
  }): Source[] {
    if (!this.db) {
      throw new Error("Database is not open");
    }

    const searchTerm = params?.searchTerm || "";
    const filter = params?.filter || "all";
    const sortedAsc = params?.sortedAsc || false;

    // Build WHERE clause conditions
    const conditions: string[] = [];
    const parameters: (string | number)[] = [];

    // Search by journalist designation
    if (searchTerm) {
      conditions.push(
        `LOWER(json_extract(data, '$.journalist_designation')) LIKE LOWER(?)`,
      );
      parameters.push(`%${searchTerm}%`);
    }

    // Filter by read status and starred status
    switch (filter) {
      case "read":
        conditions.push("is_seen = 1");
        break;
      case "unread":
        conditions.push("is_seen = 0");
        break;
      case "starred":
        conditions.push(`json_extract(data, '$.is_starred') = 1`);
        break;
      case "unstarred":
        conditions.push(`json_extract(data, '$.is_starred') = 0`);
        break;
      case "all":
      default:
        // No additional filter
        break;
    }

    // Build the WHERE clause
    const whereClause =
      conditions.length > 0 ? `WHERE ${conditions.join(" AND ")}` : "";

    // Build ORDER BY clause
    const orderDirection = sortedAsc ? "ASC" : "DESC";
    const orderClause = `ORDER BY json_extract(data, '$.last_updated') ${orderDirection}`;

    // Complete query
    const query = `
      SELECT
        uuid,
        data,
        is_seen,
        has_attachment,
        show_message_preview,
        message_preview
      FROM sources
      ${whereClause}
      ${orderClause}
    `;

    const stmt = this.db.prepare(query);
    const rows = stmt.all(...parameters) as Array<SourceRow>;

    return rows.map((row) => {
      const data = JSON.parse(row.data) as SourceMetadata;
      return {
        uuid: row.uuid,
        data,
        isRead: this.isTruthy(row.is_seen),
        hasAttachment: this.isTruthy(row.has_attachment),
        showMessagePreview: this.isTruthy(row.show_message_preview),
        messagePreview: row.message_preview,
      };
    });
  }

  getSourceWithItems(sourceUuid: string): SourceWithItems {
    if (!this.db) {
      throw new Error("Database is not open");
    }

    // Get the source data
    const sourceStmt = this.db.prepare(`
      SELECT uuid, data FROM sources
      WHERE uuid = ?;
    `);
    const sourceRow = sourceStmt.get(sourceUuid) as SourceRow | undefined;

    if (!sourceRow) {
      throw new Error(`Source with UUID ${sourceUuid} not found`);
    }

    const sourceData = JSON.parse(sourceRow.data);

    // Get the items for this source
    const itemsStmt = this.db.prepare(`
      SELECT uuid, data, plaintext, filename FROM items
      WHERE source_uuid = ?;
    `);
    const itemRows = itemsStmt.all(sourceUuid) as Array<ItemRow>;

    const items = itemRows.map((row) => {
      const data = JSON.parse(row.data) as ItemMetadata;
      return {
        uuid: row.uuid,
        data,
        plaintext: row.plaintext,
        filename: row.filename,
      };
    });

    return {
      uuid: sourceRow.uuid,
      data: sourceData as SourceMetadata,
      items,
    };
  }
}
