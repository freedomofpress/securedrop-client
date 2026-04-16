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
  SearchResult,
  FirstRunStatus,
  PendingEventData,
} from "../../types";
import { Crypto } from "../crypto";
import { Search } from "./search";

// Truncate message previews to 200 Unicode code points
// at the database layer; CSS will handle the rest
export const MESSAGE_PREVIEW_LENGTH = 200;
const DEFAULT_ITEM_LIMIT = 100;

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
  private searchIndex: Search;
  private firstRunStatus: FirstRunStatus = null;

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
  private selectMessageItemsProcessable: Statement<
    { limit: number },
    { uuid: string }
  >;
  private selectFileItemsProcessable: Statement<
    { limit: number },
    { uuid: string }
  >;
  private selectUnprojectedItemsBySource: Statement<
    { source_uuid: string },
    { uuid: string }
  >;
  private upsertItem: Statement<
    { uuid: string; data: string; version: string },
    void
  >;
  private deleteItem: Statement<{ uuid: string }, void>;
  private updateItemFetchStatus: Statement<{
    uuid: string;
    fetch_status: number;
  }>;
  private updateItemFetchStatusWithReset: Statement<{
    uuid: string;
    fetch_status: number;
  }>;
  private updateItemsFetchStatusBySource: Statement<{
    source_uuid: string;
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
  private selectJournalist: Statement<{ uuid: string }, JournalistRow>;

  private deleteJournalist: Statement<{ uuid: string }, void>;

  private selectAllSources: Statement<[], SourceRow>;
  private selectSourceById: Statement<[string], SourceRow>;
  private selectItemsBySourceId: Statement<[string, number], ItemRow>;
  private selectItemsBySourceIdBefore: Statement<
    [string, number, number],
    ItemRow
  >;
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
  private selectSourceConversationSeenEvent: Statement<
    { source_uuid: string },
    { snowflake_id: string; data: string }
  >;
  private selectUnprojectedUnseenItemsCount: Statement<
    { source_uuid: string; upper_bound: number },
    { count: number }
  >;
  private deletePendingEvent: Statement<{ snowflake_id: string }, void>;
  private selectPendingEvents: Statement<[{ limit: number }], PendingEventRow>;
  private deletePendingEventsBySource: Statement<{ source_uuid: string }, void>;
  private deletePendingEventsBySourceScope: Statement<
    { source_uuid: string },
    void
  >;
  private deletePendingEventsByItem: Statement<{ item_uuid: string }, void>;

  protected constructor(crypto: Crypto, dbDir?: string) {
    this.crypto = crypto;
    this.snowflake = new Snowflake(new Date("2000-01-01T00:00:00.000Z"));

    if (!dbDir) {
      dbDir = path.join(os.homedir(), ".config", "SecureDrop");
    }

    // Ensure the directory exists
    if (!fs.existsSync(dbDir)) {
      fs.mkdirSync(dbDir, { recursive: true });
    }

    // Check if this is a fresh database (first run)
    const dbPath = path.join(dbDir, "db.sqlite");
    const isNewDatabase = !fs.existsSync(dbPath);

    // Create or open the SQLite database
    const db = new Database(dbPath, { nativeBinding: this.getBinaryPath() });

    // enable security pragmas
    db.pragma("secure_delete = ON");
    db.pragma("auto_vacuum = FULL");

    // WAL mode must be set after auto_vacuum
    db.pragma("journal_mode = WAL");

    // Determine first-run status before migrations run
    if (isNewDatabase) {
      const legacyPath = path.join(os.homedir(), ".securedrop_client");
      this.firstRunStatus = fs.existsSync(legacyPath)
        ? "migration"
        : "new_user";
    }

    // Set the database URL for migrations
    this.url = `sqlite:${dbPath}`;
    this.db = db;

    // Run migrations (before we prepare any statements based on the latest schema)
    this.runMigrations();

    // Initialize search index
    this.searchIndex = new Search(db);

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
    this.selectMessageItemsProcessable = this.db.prepare(
      `SELECT uuid FROM items
      WHERE kind <> 'file'
        AND fetch_status in (${FetchStatus.Initial}, ${FetchStatus.DownloadInProgress}, ${FetchStatus.DecryptionInProgress}, ${FetchStatus.FailedDownloadRetryable}, ${FetchStatus.FailedDecryptionRetryable})
      ORDER BY interaction_count ASC, uuid ASC
      LIMIT @limit`,
    );
    this.selectFileItemsProcessable = this.db.prepare(
      `SELECT uuid FROM items
      WHERE kind = 'file'
        AND fetch_status in (${FetchStatus.Initial}, ${FetchStatus.DownloadInProgress}, ${FetchStatus.DecryptionInProgress}, ${FetchStatus.FailedDownloadRetryable}, ${FetchStatus.FailedDecryptionRetryable})
      ORDER BY interaction_count ASC, uuid ASC
      LIMIT @limit`,
    );
    this.selectUnprojectedItemsBySource = this.db.prepare(
      "SELECT uuid FROM items WHERE source_uuid = @source_uuid",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@id, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.updateItemFetchStatus = this.db.prepare(
      "UPDATE items SET fetch_status = @fetch_status WHERE uuid = @uuid",
    );
    this.updateItemFetchStatusWithReset = this.db.prepare(
      "UPDATE items SET fetch_status = @fetch_status, fetch_progress = 0 WHERE uuid = @uuid",
    );
    this.updateItemsFetchStatusBySource = this.db.prepare(
      "UPDATE items SET fetch_status = @fetch_status WHERE source_uuid = @source_uuid",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteItem = this.db.prepare("DELETE FROM items WHERE uuid = @uuid");
    this.selectItem = this.db.prepare(
      `SELECT uuid, data, plaintext, filename, fetch_status, fetch_progress, decrypted_size FROM items WHERE uuid = @uuid`,
    );

    this.selectAllJournalistVersion = this.db.prepare(
      "SELECT uuid, version FROM journalists",
    );

    this.selectJournalist = this.db.prepare(
      "SELECT uuid, data FROM journalists WHERE uuid = @uuid",
    );

    this.upsertJournalist = this.db.prepare(
      "INSERT INTO journalists (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteJournalist = this.db.prepare(
      "DELETE FROM journalists WHERE uuid = @uuid",
    );

    this.selectAllSources = this.db.prepare(`
      SELECT
        s.uuid,
        s.data,
        s.is_seen,
        s.has_attachment,
        i.kind AS last_message_kind,
        substr(i.plaintext, 1, ${MESSAGE_PREVIEW_LENGTH}) AS last_message_plaintext,
        i.filename AS last_message_filename,
        i.interaction_count AS last_interaction_count
      FROM sources_projected s
      LEFT JOIN sorted_items i
        ON s.uuid = i.source_uuid
        AND i.rn = 1;
    `);
    this.selectSourceById = this.db.prepare(`
      SELECT
        s.uuid,
        s.data,
        s.is_seen,
        s.has_attachment,
        i.kind AS last_message_kind,
        substr(i.plaintext, 1, ${MESSAGE_PREVIEW_LENGTH}) AS last_message_plaintext,
        i.filename AS last_message_filename,
        i.interaction_count AS last_interaction_count
      FROM sources_projected s
      LEFT JOIN sorted_items i
        ON s.uuid = i.source_uuid AND i.rn = 1
      WHERE s.uuid = ?
    `);
    this.selectItemsBySourceId = this.db.prepare(`
      SELECT uuid, data, plaintext, filename, fetch_status, fetch_progress, decrypted_size, is_read FROM items_projected
      WHERE source_uuid = ?
      ORDER BY interaction_count DESC
      LIMIT ?
    `);
    this.selectItemsBySourceIdBefore = this.db.prepare(`
      SELECT uuid, data, plaintext, filename, fetch_status, fetch_progress, decrypted_size FROM items_projected
      WHERE source_uuid = ? AND interaction_count < ?
      ORDER BY interaction_count DESC
      LIMIT ?
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

    this.selectSourceConversationSeenEvent = this.db.prepare(`
      SELECT snowflake_id, data FROM pending_events
      WHERE source_uuid = @source_uuid AND type = 'source_conversation_seen'
    `);
    this.selectUnprojectedUnseenItemsCount = this.db.prepare(`
      SELECT
        COUNT(*) AS count
      FROM items
      WHERE source_uuid = @source_uuid
        AND interaction_count <= @upper_bound
        AND is_read = 0
    `);
    this.deletePendingEvent = this.db.prepare(
      `DELETE FROM pending_events WHERE snowflake_id = @snowflake_id`,
    );
    this.selectPendingEvents = this.db.prepare(`
      SELECT snowflake_id, source_uuid, item_uuid, type, data FROM pending_events ORDER BY snowflake_id ASC LIMIT @limit
    `);
    this.deletePendingEventsBySource = this.db.prepare(`
      DELETE FROM pending_events WHERE source_uuid = @source_uuid`);
    this.deletePendingEventsBySourceScope = this.db.prepare(`
      DELETE FROM pending_events
      WHERE source_uuid = @source_uuid
         OR item_uuid IN (
           SELECT uuid FROM items WHERE source_uuid = @source_uuid
         )`);
    this.deletePendingEventsByItem = this.db.prepare(`
      DELETE FROM pending_events WHERE item_uuid = @item_uuid`);
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

  search(query: string): SearchResult[] {
    return this.searchIndex.search(query);
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
    if (values.length === 0) {
      return [];
    }

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

  protected deleteItems(items: string[]): Item[] {
    return this.db!.transaction((items: string[]) => {
      const deletedItems: Item[] = [];
      for (const itemID of items) {
        const item = this.getItem(itemID);
        if (item) {
          deletedItems.push(item);
        }
        this.searchIndex.removeItem(itemID);
        this.deletePendingEventsByItem.run({ item_uuid: itemID });
        this.deleteItem.run({ uuid: itemID });
      }
      this.updateVersion();
      return deletedItems;
    })(items);
  }

  // Delete source and any source items from the DB and search index
  private deleteSourceAndItems(sourceUuid: string): void {
    return this.db!.transaction((sourceUuid: string) => {
      // First, remove all search index entries for this source
      this.searchIndex.removeSource(sourceUuid);
      // Delete any pending events for this source
      this.deletePendingEventsBySource.run({ source_uuid: sourceUuid });
      // Delete all source items, querying from unprojected view to not
      // orphan pending deleted items
      const itemUuids = this.selectUnprojectedItemsBySource
        .all({
          source_uuid: sourceUuid,
        })
        .map((row) => row.uuid);
      this.deleteItems(itemUuids);
      // Then, delete the source
      this.deleteSource.run({ uuid: sourceUuid });
    })(sourceUuid);
  }

  protected deleteSources(sources: string[]): void {
    this.db!.transaction((sources: string[]) => {
      for (const sourceID of sources) {
        this.deleteSourceAndItems(sourceID);
      }
      this.updateVersion();
    })(sources);
  }

  protected deleteJournalists(journalists: string[]): void {
    this.db!.transaction((journalists: string[]) => {
      for (const journalistID of journalists) {
        this.deleteJournalist.run({ uuid: journalistID });
      }
      this.updateVersion();
    })(journalists);
  }

  protected updateBatch(batchResponse: BatchResponse): {
    deleted_items: Item[];
    deleted_sources: string[];
  } {
    return this.db!.transaction((batch: BatchResponse) => {
      this.updatePendingEvents(batch.events);
      const deleted_items = this.updateItems(batch.items);
      const deleted_sources = this.updateSources(batch.sources);
      this.updateJournalists(batch.journalists);
      this.updateVersion();
      return { deleted_items, deleted_sources };
    })(batchResponse);
  }

  protected updateSources(sources: {
    [uuid: string]: SourceMetadata | null;
  }): string[] {
    const deletedSourceUuids: string[] = [];
    this.db!.transaction(
      (sources: { [uuid: string]: SourceMetadata | null }) => {
        Object.keys(sources).forEach((sourceid: string) => {
          const metadata = sources[sourceid];
          if (metadata) {
            const info = JSON.stringify(metadata, sortKeys);
            const version = computeVersion(info);
            this.upsertSource.run({ uuid: sourceid, data: info, version });
            this.searchIndex.indexSource(sourceid);
          } else {
            deletedSourceUuids.push(sourceid);
            this.deleteSourceAndItems(sourceid);
          }
        });
      },
    )(sources);
    return deletedSourceUuids;
  }

  protected updateItems(items: {
    [uuid: string]: ItemMetadata | null;
  }): Item[] {
    const deletedItems: Item[] = [];
    this.db!.transaction((items: { [uuid: string]: ItemMetadata | null }) => {
      Object.keys(items).forEach((itemid: string) => {
        const metadata = items[itemid];
        if (metadata) {
          const blob = JSON.stringify(metadata, sortKeys);
          const version = computeVersion(blob);
          this.upsertItem.run({ uuid: itemid, data: blob, version });
        } else {
          const item = this.getItem(itemid);
          if (item) {
            deletedItems.push(item);
          }
          this.deleteItem.run({ uuid: itemid });
        }
      });
    })(items);
    return deletedItems;
  }

  public updateFetchStatus(itemUuid: string, fetchStatus: number) {
    // When cancelling, reset fetch_progress so the next download starts fresh
    if (fetchStatus === FetchStatus.Cancelled) {
      this.updateItemFetchStatusWithReset.run({
        uuid: itemUuid,
        fetch_status: fetchStatus,
      });
    } else {
      this.updateItemFetchStatus.run({
        uuid: itemUuid,
        fetch_status: fetchStatus,
      });
    }
  }

  // Updates journalist metadata in DB. Should be run in a transaction that also
  // updates the global index version.
  protected updateJournalists(journalists: {
    [uuid: string]: JournalistMetadata | null;
  }) {
    this.db!.transaction(
      (journalists: { [uuid: string]: JournalistMetadata | null }) => {
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
      },
    )(journalists);
  }

  // Helper function for truthy values
  private isTruthy(value: unknown): boolean {
    if (typeof value === "boolean") {
      return value;
    }
    if (typeof value === "number") {
      return value !== 0;
    }
    if (typeof value === "string") {
      return value.toLowerCase() === "true" || value === "1";
    }
    return Boolean(value);
  }

  // Helper function for handling SourceRow
  private toSource(row: SourceRow): Source {
    return {
      uuid: row.uuid,
      data: JSON.parse(row.data) as SourceMetadata,
      isRead: this.isTruthy(row.is_seen),
      hasAttachment: this.isTruthy(row.has_attachment),
      messagePreview: row.last_message_kind
        ? {
            kind: row.last_message_kind,
            plaintext:
              (row.last_message_kind === "file"
                ? row.last_message_filename?.substring(
                    row.last_message_filename.lastIndexOf("/") + 1,
                  )
                : row.last_message_plaintext) ?? null,
          }
        : null,
      lastInteractionCount: row.last_interaction_count ?? null,
    };
  }

  getSource(uuid: string): Source | null {
    const row = this.selectSourceById.get(uuid);
    if (!row) {
      return null;
    }
    return this.toSource(row);
  }

  getSources(): Source[] {
    if (!this.db) {
      throw new Error("Database is not open");
    }

    const rows = this.selectAllSources.all();
    return rows.map((row) => {
      return this.toSource(row);
    });
  }

  getSourceWithItems(
    sourceUuid: string,
    options?: {
      limit?: number;
      beforeInteractionCount?: number;
      journalistUuid?: string;
    },
  ): SourceWithItems {
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

    let limit = DEFAULT_ITEM_LIMIT;
    if (options?.limit) {
      limit = options?.limit;
    }
    // Fetch limit+1 rows to detect if there are more historical items
    const fetchLimit = limit + 1;
    let rows: ItemRow[];
    if (options?.beforeInteractionCount) {
      rows = this.selectItemsBySourceIdBefore.all(
        sourceUuid,
        options.beforeInteractionCount,
        fetchLimit,
      );
    } else {
      rows = this.selectItemsBySourceId.all(sourceUuid, fetchLimit);
    }
    const hasMoreHistoricalItems = rows.length > limit;
    // Take at most `limit` rows (DESC order), then reverse to ASC for display
    const itemRows = rows.slice(0, limit).reverse();

    const items = itemRows.map((row) => {
      const data = JSON.parse(row.data) as ItemMetadata;
      if (row.is_read !== undefined && "is_read" in data) {
        (data as { is_read: boolean }).is_read = this.isTruthy(row.is_read);
      }
      return {
        uuid: row.uuid,
        data,
        plaintext: row.plaintext,
        filename: row.filename,
        fetch_status: row.fetch_status,
        fetch_progress: row.fetch_progress,
        decrypted_size: row.decrypted_size,
      };
    });

    // Return most recently seen message: all replies are seen, if journalistUuid is specified
    // use seen_by field, otherwise fallback to the is_read field
    const journalistUuid = options?.journalistUuid;
    let maxSeenInteractionCount: number | null = null;
    for (const item of items) {
      const interaction = item.data.interaction_count ?? null;
      if (interaction === null) {
        continue;
      }
      let hasBeenSeen: boolean;
      if (journalistUuid) {
        hasBeenSeen = item.data.seen_by.includes(journalistUuid);
      } else if (item.data.kind !== "reply") {
        hasBeenSeen = item.data.is_read;
      } else {
        hasBeenSeen = true;
      }
      if (
        hasBeenSeen &&
        (maxSeenInteractionCount === null ||
          interaction > maxSeenInteractionCount)
      ) {
        maxSeenInteractionCount = interaction;
      }
    }
    // If nothing has been seen, return null
    const lastSeenInteractionCount = maxSeenInteractionCount ?? null;

    return {
      uuid: sourceRow.uuid,
      data: sourceData as SourceMetadata,
      items,
      hasMoreHistoricalItems,
      lastSeenInteractionCount,
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

  getJournalistByID(journalistUuid: string): Journalist {
    if (!this.db) {
      throw new Error("Database is not open");
    }
    const journalistRow = this.selectJournalist.get({
      uuid: journalistUuid,
    }) as JournalistRow | undefined;

    if (!journalistRow) {
      throw new Error(`Journalist with UUID ${journalistUuid} not found`);
    }

    const journalistData = JSON.parse(journalistRow.data);

    return {
      uuid: journalistRow.uuid,
      data: journalistData as JournalistMetadata,
    };
  }

  // Selects items that are ready to be downloaded + decrypted. This
  // is all messages, and files that have been initiated from the client
  // by being put into FetchStatus.DownloadInProgress
  getItemsToProcess(limits: {
    messageLimit: number;
    fileLimit: number;
  }): string[] {
    type Row = {
      uuid: string;
    };
    const messageRows = this.selectMessageItemsProcessable.all({
      limit: limits.messageLimit,
    }) as Array<Row>;
    const fileRows = this.selectFileItemsProcessable.all({
      limit: limits.fileLimit,
    }) as Array<Row>;
    return [...messageRows, ...fileRows].map((r) => r.uuid);
  }

  getItem(itemUuid: string): Item | null {
    const row = this.selectItem.get({ uuid: itemUuid });
    if (!row) {
      return null;
    }
    return {
      uuid: row.uuid,
      data: JSON.parse(row.data) as ItemMetadata,
      plaintext: row.plaintext,
      filename: row.filename,
      fetch_status: row.fetch_status as FetchStatus,
      fetch_progress: row.fetch_progress,
      decrypted_size: row.decrypted_size,
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
    this.searchIndex.indexItem(itemUuid);
  }

  completeFileItem(itemUuid: string, filename: string, decryptedSize: number) {
    const stmt: Statement<
      { uuid: string; filename: string; decrypted_size: number },
      void
    > = this.db!.prepare(
      `UPDATE items SET fetch_progress = null, fetch_status = ${FetchStatus.Complete}, filename = @filename, decrypted_size = @decrypted_size, fetch_last_updated_at = CURRENT_TIMESTAMP WHERE uuid = @uuid`,
    );
    stmt.run({
      uuid: itemUuid,
      filename: filename,
      decrypted_size: decryptedSize,
    });
    this.searchIndex.indexItem(itemUuid);
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

  private markSourceItemsScheduledDeletion(sourceUuid: string) {
    this.updateItemsFetchStatusBySource.run({
      source_uuid: sourceUuid,
      fetch_status: FetchStatus.ScheduledDeletion,
    });
  }

  private purgePendingEventsForSource(sourceUuid: string) {
    this.deletePendingEventsBySourceScope.run({
      source_uuid: sourceUuid,
    });
  }

  addPendingSourceEvent(
    sourceUuid: string,
    type: PendingEventType,
    data?: PendingEventData,
  ): string {
    return this.db!.transaction(() => {
      const snowflakeID = this.snowflake
        .generate({ timestamp: Date.now() })
        .toString();

      if (
        type === PendingEventType.SourceDeleted ||
        type === PendingEventType.SourceConversationDeleted
      ) {
        this.purgePendingEventsForSource(sourceUuid);
        this.markSourceItemsScheduledDeletion(sourceUuid);
      }

      this.insertSourcePendingEvent.run({
        snowflake_id: snowflakeID,
        source_uuid: sourceUuid,
        type: type,
        data: data ? JSON.stringify(data) : null,
      });
      return snowflakeID;
    })();
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

  addPendingSourceConversationSeen(
    sourceUuid: string,
    upperBound: number,
  ): string | null {
    return this.db!.transaction(() => {
      const unseen = this.selectUnprojectedUnseenItemsCount.get({
        source_uuid: sourceUuid,
        upper_bound: upperBound,
      })!;
      if (unseen.count == 0) {
        return null;
      }

      const existing = this.selectSourceConversationSeenEvent.get({
        source_uuid: sourceUuid,
      });

      if (existing) {
        const existingUpperBound = (
          JSON.parse(existing.data) as { upper_bound: number }
        ).upper_bound;
        if (existingUpperBound >= upperBound) {
          return null;
        }
        this.deletePendingEvent.run({ snowflake_id: existing.snowflake_id });
      }

      const snowflakeId = this.snowflake
        .generate({ timestamp: Date.now() })
        .toString();
      this.insertSourcePendingEvent.run({
        snowflake_id: snowflakeId,
        source_uuid: sourceUuid,
        type: PendingEventType.SourceConversationSeen,
        data: JSON.stringify({ upper_bound: upperBound }),
      });
      return snowflakeId;
    })();
  }

  getPendingEvents(): PendingEvent[] {
    const rows: PendingEventRow[] = this.selectPendingEvents.all({ limit: 50 });
    const pendingEvents = rows.map((r) => {
      let target: SourceTarget | ItemTarget;
      if (r.source_uuid) {
        const source = this.selectUnprojectedSourceVersion.get({
          uuid: r.source_uuid,
        });
        if (!source) {
          throw new Error(
            `Invariant violation: pending event references nonexistent source ${r.source_uuid}`,
          );
        }
        target = {
          source_uuid: r.source_uuid,
          version: source.version,
        };
      } else {
        const item = this.selectUnprojectedItemVersion.get({
          uuid: r.item_uuid,
        });
        if (!item) {
          throw new Error(
            `Invariant violation: pending event references nonexistent item ${r.item_uuid}`,
          );
        }
        target = {
          item_uuid: r.item_uuid,
          version: item.version,
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
      // For reply_sent events, upsert the item into the items table manually
      // to avoid doing a duplicate fetch from the server
      if (event.type === PendingEventType.ReplySent) {
        const replyData = JSON.parse(event.data) as ReplySentData;
        const metadataBlob = JSON.stringify(replyData.metadata, sortKeys);
        const version = computeVersion(metadataBlob);
        this.upsertItem.run({
          uuid: replyData.uuid,
          data: metadataBlob,
          version: version,
        });
        this.completePlaintextItem(replyData.uuid, replyData.plaintext);
      }
      // Once event is applied, delete from pending events table
      this.deletePendingEvent.run({ snowflake_id: event.snowflake_id });
    }
  }

  // First-run status: "new_user" or "migration" if DB was just created, null otherwise
  getFirstRunStatus(): FirstRunStatus {
    return this.firstRunStatus;
  }
}
