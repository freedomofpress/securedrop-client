import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database, { Statement } from "better-sqlite3";
import blake from "blakejs";

import {
  Index,
  SourceMetadata,
  ItemMetadata,
  MetadataResponse,
  Source,
  SourceWithItems,
  SourceRow,
  ItemRow,
  JournalistMetadata,
  Journalist,
  JournalistRow,
  FetchStatus,
} from "../../types";

interface KeyObject {
  [key: string]: object;
}

const sortKeys = (_: string, value: KeyObject) =>
  value instanceof Object && !(value instanceof Array)
    ? Object.keys(value)
        .sort()
        .reduce((sorted: KeyObject, key: string) => {
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
    { uuid: string; data: string; version: string },
    void
  >;
  private deleteSource: Statement<{ uuid: string }, void>;

  private selectAllItemVersion: Statement<
    [],
    { uuid: string; version: string }
  >;
  private selectItemFilenameSource: Statement<
    { uuid: string },
    { filename: string; source_uuid: string }
  >;
  private upsertItem: Statement<
    { uuid: string; data: string; version: string },
    void
  >;
  private deleteItem: Statement<{ uuid: string }, void>;

  private selectAllJournalistVersion: Statement<
    [],
    { uuid: string; version: string }
  >;
  private upsertJournalist: Statement<
    { uuid: string; data: string; version: string },
    void
  >;
  private deleteJournalist: Statement<{ uuid: string }, void>;

  private selectAllSources: Statement<[], SourceRow>;
  private selectSourceById: Statement<[string], SourceRow>;
  private selectItemsBySourceId: Statement<[string], ItemRow>;
  private selectAllJournalists: Statement<[], JournalistRow>;

  constructor(dbDir?: string) {
    if (!dbDir) {
      dbDir = path.join(os.homedir(), ".config", "SecureDrop");
    }
    // Ensure the directory exists
    if (!fs.existsSync(dbDir)) {
      fs.mkdirSync(dbDir, { recursive: true });
    }

    // Create or open the SQLite database
    const dbPath = path.join(dbDir, "db.sqlite");
    const db = new Database(dbPath, { nativeBinding: this.getBinaryPath() });
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
      "INSERT INTO sources (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteSource = this.db.prepare(
      "DELETE FROM sources WHERE uuid = @uuid",
    );

    this.selectAllItemVersion = this.db.prepare(
      "SELECT uuid, version FROM items",
    );
    this.selectItemFilenameSource = this.db.prepare(
      "SELECT filename, source_uuid FROM items WHERE source_uuid = @uuid",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteItem = this.db.prepare("DELETE FROM items WHERE uuid = @uuid");
    this.selectAllJournalistVersion = this.db.prepare(
      "SELECT uuid, version FROM journalists",
    );
    this.upsertJournalist = this.db.prepare(
      "INSERT INTO journalists (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteJournalist = this.db.prepare(
      "DELETE FROM journalists WHERE uuid = @uuid",
    );

    this.selectAllSources = this.db.prepare(`
      SELECT
        uuid,
        data,
        is_seen,
        has_attachment,
        show_message_preview,
        message_preview
      FROM sources
    `);
    this.selectSourceById = this.db.prepare(`
      SELECT uuid, data FROM sources
      WHERE uuid = ?
    `);
    this.selectItemsBySourceId = this.db.prepare(`
      SELECT uuid, data, plaintext, filename FROM items
      WHERE source_uuid = ?
    `);
    this.selectAllJournalists = this.db.prepare(`
      SELECT uuid, data FROM journalists
    `);
  }

  // Detect runtime environment
  private isElectron(): boolean {
    return (
      typeof process !== "undefined" &&
      process.versions !== undefined &&
      process.versions.electron !== undefined
    );
  }

  // Get binary path for current runtime
  private getBinaryPath(): string {
    const runtime = this.isElectron() ? "electron" : "node";
    const isPackaged = __dirname.includes("app.asar");
    const basePath = isPackaged
      ? path.join(process.resourcesPath, "app.asar.unpacked")
      : process.cwd();
    const binaryPath = path.join(
      basePath,
      "node_modules",
      "better-sqlite3",
      "build",
      `Release-${runtime}`,
      "better_sqlite3.node",
    );
    console.log(
      `Loading better-sqlite3 from ${binaryPath} (packaged: ${isPackaged})`,
    );
    return binaryPath;
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
    const index: Index = { sources: {}, items: {}, journalists: {} };
    for (const row of this.selectAllSourceVersion.iterate()) {
      index.sources[row.uuid] = row.version;
    }
    for (const row of this.selectAllItemVersion.iterate()) {
      index.items[row.uuid] = row.version;
    }
    for (const row of this.selectAllJournalistVersion.iterate()) {
      index.journalists[row.uuid] = row.version;
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

  getItemFileData(itemID: string):
    | {
        filename: string;
        source_uuid: string;
      }
    | undefined {
    return this.selectItemFilenameSource.get({ uuid: itemID });
  }

  deleteItems(items: string[]) {
    this.db!.transaction((items: string[]) => {
      for (const itemID of items) {
        this.deleteItem.run({ uuid: itemID });
      }
      this.updateVersion();
    })(items);
  }

  deleteSources(sources: string[]) {
    this.db!.transaction((sources: string[]) => {
      for (const sourceID of sources) {
        this.deleteSource.run({ uuid: sourceID });
      }
      this.updateVersion();
    })(sources);
  }

  deleteJournalists(journalists: string[]) {
    this.db!.transaction((journalists: string[]) => {
      for (const journalistID of journalists) {
        this.deleteJournalist.run({ uuid: journalistID });
      }
      this.updateVersion();
    })(journalists);
  }

  updateMetadata(metadata: MetadataResponse) {
    this.db!.transaction((metadata: MetadataResponse) => {
      this.updateSources(metadata.sources);
      this.updateItems(metadata.items);
      this.updateJournalists(metadata.journalists);
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
        uuid: sourceid,
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
        uuid: itemid,
        data: blob,
        version: version,
      });
    });
  }

  // Updates journalist metadata in DB. Should be run in a transaction that also
  // updates the global index version.
  private updateJournalists(journalists: {
    [uuid: string]: JournalistMetadata;
  }) {
    Object.keys(journalists).forEach((id: string) => {
      const metadata = journalists[id];
      const blob = JSON.stringify(metadata, sortKeys);
      const version = computeVersion(blob);
      this.upsertJournalist.run({
        uuid: id,
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

  getSources(): Source[] {
    if (!this.db) {
      throw new Error("Database is not open");
    }

    const rows = this.selectAllSources.all();

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

    const sourceRow = this.selectSourceById.get(sourceUuid) as
      | SourceRow
      | undefined;

    if (!sourceRow) {
      throw new Error(`Source with UUID ${sourceUuid} not found`);
    }

    const sourceData = JSON.parse(sourceRow.data);

    const itemRows = this.selectItemsBySourceId.all(sourceUuid);

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

  getJournalists(): Journalist[] {
    if (!this.db) {
      throw new Error("Database is not open");
    }

    const rows = this.selectAllJournalists.all();

    return rows.map((row) => {
      const data = JSON.parse(row.data) as JournalistMetadata;
      return {
        uuid: row.uuid,
        data,
      };
    });
  }

  getItemsToProcess(): string[] {
    type Row = {
      uuid: string;
    };
    console.log("getting items to process");
    const itemStmt = this.db!.prepare(`
      SELECT uuid FROM items
      WHERE fetch_status IN (${FetchStatus.Initial}, ${FetchStatus.DownloadInProgress}, ${FetchStatus.FailedDownloadRetryable}, ${FetchStatus.FailedDecryptionRetryable})
    `);
    const rows = itemStmt?.all() as Array<Row>;
    return rows.map((r) => r.uuid);
  }

  getItemWithFetchStatus(
    itemUuid: string,
  ): [ItemMetadata, FetchStatus, number] {
    type Row = {
      data: string;
      fetch_status: number;
      fetch_progress: number;
    };
    const itemStmt = this.db?.prepare(`
      SELECT data, fetch_status, fetch_progress FROM items WHERE uuid = ?`);
    const item = itemStmt?.get(itemUuid) as Row;
    return [
      JSON.parse(item.data) as ItemMetadata,
      item.fetch_status as FetchStatus,
      item.fetch_progress,
    ];
  }

  completePlaintextItem(itemUuid: string, plaintext: string) {
    const stmt: Statement<{ uuid: string; plaintext: string }, void> =
      this.db!.prepare(
        `UPDATE items SET fetch_progress = null, fetch_status = ${FetchStatus.Complete}, plaintext = @plaintext, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
      );
    stmt.run({
      uuid: itemUuid,
      plaintext: plaintext,
    });
  }

  completeFileItem(itemUuid: string, filename: string) {
    const stmt: Statement<{ uuid: string; filename: string }, void> =
      this.db!.prepare(
        `UPDATE items SET fetch_progress = null, fetch_status = ${FetchStatus.Complete}, filename = @filename, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
      );
    stmt.run({
      uuid: itemUuid,
      filename: filename,
    });
  }

  terminallyFailItem(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE ITEMS set fetch_status = ${FetchStatus.FailedTerminal}, fetch_retry_attempts = fetch_retry_attempts + 1, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }

  pauseItem(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE ITEMS set fetch_status = ${FetchStatus.Paused}, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }

  resumeItem(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE ITEMS set fetch_status = ${FetchStatus.DownloadInProgress}, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }

  setDownloadInProgress(itemUuid: string, progress?: number) {
    if (progress !== undefined) {
      const stmt: Statement<{ uuid: string; progress: number }, void> =
        this.db!.prepare(
          `UPDATE items SET fetch_progress = @progress, fetch_status = ${FetchStatus.DownloadInProgress}, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
        );
      stmt.run({
        uuid: itemUuid,
        progress: progress,
      });
    } else {
      const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
        `UPDATE items SET fetch_status = ${FetchStatus.DownloadInProgress}, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
      );
      stmt.run({ uuid: itemUuid });
    }
  }

  setDecryptionInProgress(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE items SET fetch_status = ${FetchStatus.DecryptionInProgress}, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }

  failDownload(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE items SET fetch_status = ${FetchStatus.FailedDownloadRetryable}, fetch_retry_attempts = fetch_retry_attempts + 1, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }

  failDecryption(itemUuid: string) {
    const stmt: Statement<{ uuid: string }, void> = this.db!.prepare(
      `UPDATE items SET fetch_status = ${FetchStatus.FailedDecryptionRetryable}, fetch_retry_attempts = fetch_retry_attempts + 1, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({ uuid: itemUuid });
  }
}
