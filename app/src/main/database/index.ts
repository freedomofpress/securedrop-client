import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database, { Statement } from "better-sqlite3";
import blake from "blakejs";

import {
  Index,
  ItemVersions,
  SourceMetadata,
  SourceSyncResponse,
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
  private deleteVersion: Statement<[], void>;
  private insertVersion: Statement<[string], void>;

  private selectAllSourceVersion: Statement<
    [],
    { uuid: string; version: string; data: string }
  >;
  private selectSourceData: Statement<[string], { data: string }>;
  private upsertSource: Statement<
    { uuid: string; data: string; version: string },
    void
  >;

  private selectItemVersion: Statement<
    [string],
    { uuid: string; version: string }
  >;
  private upsertItem: Statement<
    { uuid: string; data: string; version: string },
    void
  >;

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
      "SELECT uuid, version, data FROM sources",
    );
    this.selectSourceData = this.db.prepare(
      "SELECT data FROM sources WHERE uuid = ?",
    );
    this.upsertSource = this.db.prepare(
      "INSERT INTO sources (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );

    this.selectItemVersion = this.db.prepare(
      "SELECT version FROM items WHERE uuid = ?",
    );
    this.upsertItem = this.db.prepare(
      "INSERT INTO items (uuid, data, version) VALUES (@uuid, @data, @version) ON CONFLICT(uuid) DO UPDATE SET data=@data, version=@version",
    );
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
      const sourceMetadata = JSON.parse(row.data) as SourceMetadata;
      Object.keys(sourceMetadata.collection).forEach((itemUUID) => {
        const item = this.selectItemVersion.get(itemUUID);
        if (item) {
          source.collection[itemUUID] = item.version;
        }
      });

      index.sources[row.uuid] = source;
    }

    return index;
  }

  getSourceItemVersions(id: string): ItemVersions | null {
    const row = this.selectSourceData.get(id);
    if (!row) {
      return null;
    }
    const sourceData = JSON.parse(row.data) as SourceMetadata;

    const itemVersions = {};
    Object.keys(sourceData.collection).forEach((itemUUID) => {
      const itemRow = this.selectItemVersion.get(itemUUID);
      if (itemRow) {
        itemVersions[itemUUID] = itemRow.version;
      }
    });
    return itemVersions;
  }

  updateVersion() {
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

  updateSources(sources: SourceSyncResponse) {
    Object.keys(sources.sources).forEach((sourceUUID: string) => {
      const source = sources.sources[sourceUUID];
      // Updating the full source
      if (source.info) {
        const metadata = JSON.stringify(source, sortKeys);
        const version = computeVersion(JSON.stringify(source.info, sortKeys));
        this.upsertSource.run({
          uuid: sourceUUID,
          data: metadata,
          version: version,
        });
      }
      Object.keys(source.collection).forEach((itemUUID: string) => {
        const data = JSON.stringify(source.collection[itemUUID], sortKeys);
        const version = computeVersion(data);
        this.upsertItem.run({
          uuid: itemUUID,
          data: data,
          version: version,
        });
      });
    });
    this.updateVersion();
    return;
  }
}
