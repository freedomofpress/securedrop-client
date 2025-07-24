import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database, { Statement } from "better-sqlite3";
import blake from "blakejs";

import { Index, ItemVersions, SourceDeltaResponse } from "../../types";

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
  private deleteVersion: Statement<[], void>;
  private insertVersion: Statement<[string], void>;

  private selectAllSourceVersion: Statement<
    [],
    { id: string; version: string; data: string }
  >;
  private upsertSource: Statement<
    { id: string; data: string; version: string },
    void
  >;
  private deleteSource: Statement<{ id: string }, void>;

  private selectItemVersionsBySource: Statement<
    { sourceID: string },
    { id: string; version: string }
  >;
  private upsertItem: Statement<
    { id: string; sourceID: string; data: string; version: string },
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

    // Prepare statements
    this.selectVersion = this.db.prepare("SELECT version FROM version");
    this.deleteVersion = this.db.prepare("DELETE FROM version");
    this.insertVersion = this.db.prepare(
      "INSERT INTO version (version) VALUES (?)",
    );

    this.selectAllSourceVersion = this.db.prepare(
      "SELECT id, version, data FROM sources",
    );
    this.upsertSource = this.db.prepare(
      "INSERT INTO sources (id, data, version) VALUES (@id, @data, @version) ON CONFLICT(id) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteSource = this.db.prepare("DELETE FROM sourecs WHERE id = @id");

    this.selectItemVersionsBySource = this.db.prepare(
      "SELECT id, version FROM items WHERE source_id = @source_id",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (id, source_id, data, version) VALUES (@id, @source_id, @data, @version) ON CONFLICT(id, source_id) DO UPDATE SET data=@data, version=@version",
    );
    this.deleteItem = this.db.prepare("DELETE FROM items WHERE id = @id");
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
    const index = { sources: {} };
    for (const row of this.selectAllSourceVersion.iterate()) {
      const source = {
        version: row.version,
        collection: {},
      };
      for (const item of this.selectItemVersionsBySource.iterate({
        sourceID: row.id,
      })) {
        source.collection[item.id] = item.version;
      }
      index.sources[row.id] = source;
    }

    return index;
  }

  getSourceItemVersions(sourceID: string): ItemVersions | null {
    const itemVersions: ItemVersions = {};
    for (const row of this.selectItemVersionsBySource.iterate({
      sourceID: sourceID,
    })) {
      itemVersions[row.id] = row.version;
    }
    return itemVersions;
  }

  // Updates the index version: should be called on any write operation to
  // sources or items
  private updateVersion() {
    const index = this.getIndex();
    const strIndex = JSON.stringify(index, sortKeys);
    const newVersion = computeVersion(strIndex);
    const replaceVersion = this.db?.transaction((version) => {
      this.deleteVersion.run();
      this.insertVersion.run(version);
    });
    if (replaceVersion) {
      replaceVersion(newVersion);
    }
  }

  deleteItems(items: string[]) {
    for (const itemID in items) {
      this.deleteItem.run({ id: itemID });
    }
    this.updateVersion();
  }

  deleteSources(sources: string[]) {
    for (const sourceID in sources) {
      this.deleteSource.run({ id: sourceID });
      for (const itemRow of this.selectItemVersionsBySource.iterate({
        sourceID: sourceID,
      })) {
        this.deleteItem.run({ id: itemRow.id });
      }
    }
    this.updateVersion();
  }

  updateSources(sources: SourceDeltaResponse) {
    Object.keys(sources.sources).forEach((sourceid: string) => {
      const source = sources.sources[sourceid];
      // Updating the full source: update metadata and re-compute source version
      if (source.info) {
        const info = JSON.stringify(source.info, sortKeys);
        const version = computeVersion(info);
        this.upsertSource.run({
          id: sourceid,
          data: info,
          version: version,
        });
      }
      Object.keys(source.collection).forEach((itemid: string) => {
        const data = JSON.stringify(source.collection[itemid], sortKeys);
        const version = computeVersion(data);
        this.upsertItem.run({
          id: itemid,
          sourceID: sourceid,
          data: data,
          version: version,
        });
      });
    });
    this.updateVersion();
    return;
  }
}
