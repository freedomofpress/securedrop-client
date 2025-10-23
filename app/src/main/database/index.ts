import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database, { Statement } from "better-sqlite3";
import blake from "blakejs";
import { Snowflake } from "@sapphire/snowflake";

import {
  Index,
  SourceMetadata,
  ItemMetadata,
  Source,
  SourceWithItems,
  SourceRow,
  ItemRow,
  JournalistMetadata,
  Journalist,
  JournalistRow,
  FetchStatus,
  Item,
  PendingEventType,
  ReplySentData,
  PendingEvent,
  PendingEventRow,
  SourceTarget,
  ItemTarget,
  BatchResponse,
  EventStatus,
} from "../../types";
import { Crypto } from "../crypto";

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
  private snowflake: Snowflake;
  private crypto: Crypto;

  // Prepared statements
  private selectVersion: Statement<[], { version: string }>;
  private insertVersion: Statement<[string], void>;

  private selectAllSourceVersion: Statement<
    [],
    { uuid: string; version: string }
  >;
  private selectUnprojectedSourceVersion: Statement<
    { uuid: string },
    { version: string }
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
  private selectUnprojectedItemVersion: Statement<
    { uuid: string },
    { version: string }
  >;
  private selectItemsProcessable: Statement<[], { uuid: string }>;
  private upsertItem: Statement<
    { uuid: string; data: string; version: string; fetch_status: number },
    void
  >;
  private deleteItem: Statement<{ uuid: string }, void>;
  private updateItemFetchStatus: Statement<{
    uuid: string;
    fetch_status: number;
  }>;
  private selectItem: Statement<{ uuid: string }, ItemRow>;

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
  private insertSourcePendingEvent: Statement<
    {
      snowflake_id: string;
      source_uuid: string;
      type: string;
      data: string | null;
    },
    void
  >;
  private insertItemPendingEvent: Statement<
    {
      snowflake_id: string;
      item_uuid?: string;
      type: string;
      data: string | null;
    },
    void
  >;
  private upsertPendingSeenItemEvent: Statement<
    {
      snowflake_id: bigint;
      source_uuid: string;
      item_uuid: string;
      type: string;
    },
    void
  >;
  private deletePendingEvent: Statement<{ snowflake_id: string }, void>;
  private selectPendingEvents: Statement<[], PendingEventRow>;

  constructor(crypto: Crypto, dbDir?: string) {
    this.crypto = crypto;
    this.snowflake = new Snowflake(new Date("2000-01-01T00:00:00.000Z"));

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
      "SELECT uuid, version FROM sources_projected",
    );
    this.selectUnprojectedSourceVersion = this.db.prepare(
      "SELECT version FROM sources WHERE uuid = @uuid",
    );
    this.upsertSource = this.db.prepare(
      "INSERT INTO sources (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteSource = this.db.prepare(
      "DELETE FROM sources WHERE uuid = @uuid",
    );

    this.selectAllItemVersion = this.db.prepare(
      "SELECT uuid, version FROM items_projected",
    );
    this.selectUnprojectedItemVersion = this.db.prepare(
      "SELECT version FROM items WHERE uuid = @uuid",
    );
    this.selectItemsProcessable = this.db.prepare(
      `SELECT uuid FROM items
      WHERE
        (kind = 'file' AND fetch_status in (${FetchStatus.DownloadInProgress}, ${FetchStatus.DecryptionInProgress}, ${FetchStatus.FailedDownloadRetryable}, ${FetchStatus.FailedDecryptionRetryable}))
        OR
        (kind <> 'file' AND fetch_status in (${FetchStatus.Initial}, ${FetchStatus.DownloadInProgress}, ${FetchStatus.DecryptionInProgress}, ${FetchStatus.FailedDownloadRetryable}, ${FetchStatus.FailedDecryptionRetryable}))`,
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version, fetch_status) VALUES (@id, @data, @version, @fetch_status) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version, fetch_status=@fetch_status",
    );
    this.updateItemFetchStatus = this.db.prepare(
      "UPDATE items SET fetch_status = @fetch_status WHERE uuid = @uuid",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteItem = this.db.prepare("DELETE FROM items WHERE uuid = @uuid");
    this.selectItem = this.db.prepare(
      `SELECT uuid, data, plaintext, filename, fetch_status, fetch_progress FROM items WHERE uuid = @uuid`,
    );

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
      FROM sources_projected
    `);
    this.selectSourceById = this.db.prepare(`
      SELECT uuid, data FROM sources_projected
      WHERE uuid = ?
    `);
    this.selectItemsBySourceId = this.db.prepare(`
      SELECT uuid, data, plaintext, filename, fetch_status, fetch_progress FROM items_projected
      WHERE source_uuid = ?
      ORDER BY interaction_count ASC
    `);
    this.selectAllJournalists = this.db.prepare(`
      SELECT uuid, data FROM journalists
    `);

    this.insertSourcePendingEvent = this.db.prepare(`
      INSERT INTO pending_events (snowflake_id, source_uuid, type, data) VALUES (@snowflake_id, @source_uuid, @type, @data)
    `);

    this.insertItemPendingEvent = this.db.prepare(`
      INSERT INTO pending_events (snowflake_id, item_uuid, type, data) VALUES(@snowflake_id, @item_uuid, @type, @data)
    `);

    this.upsertPendingSeenItemEvent = this.db.prepare(`
      INSERT INTO pending_events (snowflake_id, item_uuid, type)
      SELECT @snowflake_id, @item_uuid, @type
      WHERE EXISTS (
        SELECT 1 FROM items
        WHERE uuid = @item_uuid AND source_uuid = @source_uuid
      )
      AND NOT EXISTS (
        SELECT 1 FROM pending_events
        WHERE item_uuid = @item_uuid AND type = @type
      )
        `);
    this.deletePendingEvent = this.db.prepare(
      `DELETE FROM pending_events WHERE snowflake_id = @snowflake_id`,
    );
    this.selectPendingEvents = this.db.prepare(`
      SELECT snowflake_id, source_uuid, item_uuid, type, data FROM pending_events
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

  // Select rows from a table where the specified column matches any value in an array.
  // Allows for multi-select with an array of IDs
  // Any new table/column must be added to the allowlist here as a string literal type to
  // ensure it's hardcoded and not user input.
  selectWhereIn<T>(
    table: "pending_events",
    column: "snowflake_id",
    values: (string | number)[],
  ): T[] {
    if (values.length === 0) return [];

    // Build placeholders (?, ?, ?, ...)
    const placeholders = values.map(() => "?").join(", ");

    const stmt = this.db!.prepare(
      `SELECT * FROM ${table} WHERE ${column} IN (${placeholders})`,
    );
    return stmt.all(...values) as T[];
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

  deleteItems(items: string[]) {
    this.db!.transaction((items: string[]) => {
      for (const itemID of items) {
        this.deleteItem.run({ uuid: itemID });
      }
      this.updateVersion();
    })(items);
  }

  deleteSourceAndItems(sourceUuid: string) {
    // First, delete all source items
    const items = this.selectItemsBySourceId.all(sourceUuid);
    const itemUuids: string[] = items.map((item) => {
      return item.uuid;
    });
    this.deleteItems(itemUuids);
    // Then, delete the source
    this.deleteSource.run({ uuid: sourceUuid });
  }

  deleteSources(sources: string[]) {
    this.db!.transaction((sources: string[]) => {
      for (const sourceID of sources) {
        this.deleteSourceAndItems(sourceID);
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

  updateBatch(batchResponse: BatchResponse) {
    this.db!.transaction((batch: BatchResponse) => {
      this.updatePendingEvents(batch.events);
      this.updateItems(batch.items);
      this.updateSources(batch.sources);
      this.updateJournalists(batch.journalists);
      this.updateVersion();
    })(batchResponse);
  }

  // Updates source versions in DB. Should be run in a transaction that also
  // updates the global index version.
  updateSources(sources: { [uuid: string]: SourceMetadata }) {
    Object.keys(sources).forEach((sourceid: string) => {
      const metadata = sources[sourceid];
      if (metadata) {
        // Updating the full source: update metadata and re-compute source version
        const info = JSON.stringify(metadata, sortKeys);
        const version = computeVersion(info);
        this.upsertSource.run({
          uuid: sourceid,
          data: info,
          version: version,
        });
      } else {
        this.deleteSourceAndItems(sourceid);
      }
    });
  }

  // Updates item versions in DB. Should be run in a transaction that also
  // updates the global index version.
  updateItems(items: { [uuid: string]: ItemMetadata }) {
    Object.keys(items).forEach((itemid: string) => {
      const metadata = items[itemid];
      if (metadata) {
        const blob = JSON.stringify(metadata, sortKeys);
        const version = computeVersion(blob);

        this.upsertItem.run({
          uuid: itemid,
          data: blob,
          version: version,
          fetch_status: FetchStatus.Initial,
        });
      } else {
        this.deleteItem.run({ uuid: itemid });
      }
    });
  }

  public updateFetchStatus(itemUuid: string, fetchStatus: number) {
    this.updateItemFetchStatus.run({
      uuid: itemUuid,
      fetch_status: fetchStatus,
    });
  }

  // Updates journalist metadata in DB. Should be run in a transaction that also
  // updates the global index version.
  private updateJournalists(journalists: {
    [uuid: string]: JournalistMetadata;
  }) {
    Object.keys(journalists).forEach((id: string) => {
      const metadata = journalists[id];
      if (metadata) {
        const blob = JSON.stringify(metadata, sortKeys);
        const version = computeVersion(blob);
        this.upsertJournalist.run({
          uuid: id,
          data: blob,
          version: version,
        });
      } else {
        this.deleteJournalist.run({ uuid: id });
      }
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
        fetch_status: row.fetch_status,
        fetch_progress: row.fetch_progress,
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

  // Selects items that are ready to be downloaded + decrypted. This
  // is all messages, and files that have been initiated from the client
  // by being put into FetchStatus.DownloadInProgress
  getItemsToProcess(): string[] {
    type Row = {
      uuid: string;
    };
    const rows = this.selectItemsProcessable.all() as Array<Row>;
    return rows.map((r) => r.uuid);
  }

  getItem(itemUuid: string): Item {
    const row = this.selectItem.get({ uuid: itemUuid }) as ItemRow;
    return {
      uuid: row.uuid,
      data: JSON.parse(row.data) as ItemMetadata,
      plaintext: row.plaintext,
      filename: row.filename,
      fetch_status: row.fetch_status as FetchStatus,
      fetch_progress: row.fetch_progress,
    };
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

  addPendingSourceEvent(sourceUuid: string, type: PendingEventType): string {
    const snowflakeID = this.snowflake
      .generate({ timestamp: Date.now() })
      .toString();
    this.insertSourcePendingEvent.run({
      snowflake_id: snowflakeID,
      source_uuid: sourceUuid,
      type: type,
      data: null,
    });
    return snowflakeID;
  }

  async addPendingReplySentEvent(
    text: string,
    sourceUuid: string,
    interactionCount: number,
  ): Promise<string> {
    const itemUuid = crypto.randomUUID();
    const snowflakeID = this.snowflake
      .generate({ timestamp: Date.now() })
      .toString();

    const source = this.selectSourceById.get(sourceUuid);
    if (!source || !source.data) {
      return Promise.reject("no source metadata: cannot send reply");
    }
    const sourceMetadata: SourceMetadata = JSON.parse(source.data);

    const replyData: ReplySentData = {
      uuid: itemUuid,
      metadata: {
        kind: "reply",
        uuid: itemUuid,
        source: sourceUuid,
        size: text.length,
        // The server sets the journalist_uuid when processing the event
        journalist_uuid: "",
        is_deleted_by_source: false,
        seen_by: [],
        interaction_count: interactionCount,
      },
      plaintext: text,
      reply: await this.crypto.encryptSourceMessage(
        text,
        sourceMetadata.public_key,
      ),
    };

    this.insertSourcePendingEvent.run({
      snowflake_id: snowflakeID,
      source_uuid: sourceUuid,
      type: PendingEventType.ReplySent,
      data: JSON.stringify(replyData, sortKeys),
    });
    return snowflakeID;
  }

  addPendingItemEvent(itemUuid: string, type: PendingEventType): string {
    const snowflakeID = this.snowflake
      .generate({ timestamp: Date.now() })
      .toString();
    this.insertItemPendingEvent.run({
      snowflake_id: snowflakeID,
      item_uuid: itemUuid,
      type: type,
      data: null,
    });
    return snowflakeID;
  }

  addPendingItemsSeenBatch(sourceUuid: string, itemUuids: string[]): bigint[] {
    return this.db!.transaction(() => {
      const snowflakeIds: bigint[] = [];

      for (const itemUuid of itemUuids) {
        const snowflakeId = this.snowflake.generate({ timestamp: Date.now() });

        // Conditionally insert Seen event only if:
        // 1. Item belongs to the specified source
        // 2. No Seen event exists for this item yet
        const info = this.upsertPendingSeenItemEvent.run({
          snowflake_id: snowflakeId,
          source_uuid: sourceUuid,
          item_uuid: itemUuid,
          type: PendingEventType.Seen,
        });

        // Only add to results if the insert actually happened
        if (info.changes > 0) {
          snowflakeIds.push(snowflakeId);
        }
      }

      return snowflakeIds;
    })();
  }

  getPendingEvents(): PendingEvent[] {
    const rows: PendingEventRow[] = this.selectPendingEvents.all();
    const pendingEvents = rows.map((r) => {
      let target: SourceTarget | ItemTarget;
      if (r.source_uuid) {
        target = {
          source_uuid: r.source_uuid,
          version:
            this.selectUnprojectedSourceVersion.get({ uuid: r.source_uuid })
              ?.version ?? "",
        };
      } else {
        target = {
          item_uuid: r.item_uuid,
          version:
            this.selectUnprojectedItemVersion.get({ uuid: r.item_uuid })
              ?.version ?? "",
        };
      }
      return {
        id: r.snowflake_id,
        type: r.type as PendingEventType,
        target: target,
        data: JSON.parse(r.data),
      };
    });
    return pendingEvents;
  }

  // Takes pending events and their statuses from the server and applies
  // pending event updates as needed.
  // Should be run within a transaction that also updates index version.
  updatePendingEvents(events: {
    [snowflake_id: string]: [number, string | null];
  }) {
    // Remove successfully applied pending events. On failure, retain them in the
    // pending events table for resubmission on next sync
    const appliedEventIDs: string[] = [];
    const eventIDsToRemove: string[] = [];
    Object.keys(events).forEach((snowflake_id: string) => {
      const result = events[snowflake_id][0];
      if (result === EventStatus.OK) {
        appliedEventIDs.push(snowflake_id);
      }
      if (result === EventStatus.AlreadyReported) {
        eventIDsToRemove.push(snowflake_id);
      }
    });

    for (const eventID of eventIDsToRemove) {
      this.deletePendingEvent.run({ snowflake_id: eventID });
    }

    const eventsToApply: PendingEventRow[] = this.selectWhereIn(
      "pending_events",
      "snowflake_id",
      appliedEventIDs,
    );
    for (const event of eventsToApply) {
      // Once event is applied, delete from pending events table
      this.deletePendingEvent.run({ snowflake_id: event.snowflake_id });
    }
  }
}
