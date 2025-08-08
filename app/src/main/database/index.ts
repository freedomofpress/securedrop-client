import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database from "better-sqlite3";

import type {
  Source,
  SourceWithItems,
  SourceObj,
  SourceRow,
  ItemObj,
  ItemRow,
} from "../../types";

let db: Database.Database | null = null;
let databaseUrl: string | null = null;

export const openDatabase = (): Database.Database => {
  if (db) {
    return db;
  }

  // Ensure the directory exists
  const dbDir = path.join(os.homedir(), ".config", "SecureDrop");
  if (!fs.existsSync(dbDir)) {
    fs.mkdirSync(dbDir, { recursive: true });
  }

  // Create or open the SQLite database
  const dbPath = path.join(dbDir, "db.sqlite");
  db = new Database(dbPath, {});
  db.pragma("journal_mode = WAL");

  // Set the database URL for migrations
  databaseUrl = `sqlite:${dbPath}`;
  return db;
};

export const runMigrations = () => {
  if (!databaseUrl) {
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
      `--url "${databaseUrl}"`,
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
};

export const closeDatabase = () => {
  if (db) {
    db.close();
    db = null;
  }
};

// eslint-disable-next-line @typescript-eslint/no-explicit-any
const isTruthy = (value: any): boolean => {
  if (typeof value === "boolean") return value;
  if (typeof value === "number") return value !== 0;
  if (typeof value === "string")
    return value.toLowerCase() === "true" || value === "1";
  return Boolean(value);
};

export const getSources = (): Source[] => {
  if (!db) {
    throw new Error("Database is not open");
  }

  // Select sources
  const stmt = db.prepare(`
    SELECT
      uuid,
      data,
      is_seen,
      has_attachment,
      show_message_preview,
      message_preview
    FROM sources
  `);

  const rows = stmt.all() as Array<SourceRow>;

  return rows.map((row) => {
    const data = JSON.parse(row.data);
    return {
      uuid: row.uuid,
      data: {
        isStarred: data.is_starred,
        journalistDesignation: data.journalist_designation,
        lastUpdated: data.last_updated,
        publicKey: data.public_key,
        fingerprint: data.fingerprint,
        uuid: data.uuid,
      } as SourceObj,
      isRead: isTruthy(row.is_seen),
      hasAttachment: isTruthy(row.has_attachment),
      showMessagePreview: isTruthy(row.show_message_preview),
      messagePreview: row.message_preview,
    };
  });
};

export const getSourceWithItems = (sourceUuid: string): SourceWithItems => {
  if (!db) {
    throw new Error("Database is not open");
  }

  // Get the source data
  const sourceStmt = db.prepare(`
    SELECT uuid, data FROM sources
    WHERE uuid = ?;
  `);
  const sourceRow = sourceStmt.get(sourceUuid) as SourceRow | undefined;

  if (!sourceRow) {
    throw new Error(`Source with UUID ${sourceUuid} not found`);
  }

  const sourceData = JSON.parse(sourceRow.data);

  // Get the items for this source
  const itemsStmt = db.prepare(`
    SELECT uuid, data, plaintext, filename FROM items
    WHERE source_uuid = ?;
  `);
  const itemRows = itemsStmt.all(sourceUuid) as Array<ItemRow>;

  const items = itemRows.map((row) => {
    const data = JSON.parse(row.data);
    return {
      uuid: row.uuid,
      data: {
        uuid: data.uuid,
        kind: data.kind,
        seenBy: data.seen_by,
        size: data.size,
        source: data.source,
        // Only include isRead for messages and files
        ...(data.kind !== "reply" && { isRead: data.is_read }),
        // Only include isDeletedBySource for replies
        ...(data.kind === "reply" && {
          isDeletedBySource: data.is_deleted_by_source,
        }),
      } as ItemObj,
      plaintext: row.plaintext,
      filename: row.filename,
    };
  });

  return {
    uuid: sourceRow.uuid,
    data: {
      isStarred: isTruthy(sourceData.is_starred),
      journalistDesignation: sourceData.journalist_designation,
      lastUpdated: sourceData.last_updated,
      publicKey: sourceData.public_key,
      fingerprint: sourceData.fingerprint,
      uuid: sourceData.uuid,
    } as SourceObj,
    items,
  };
};
