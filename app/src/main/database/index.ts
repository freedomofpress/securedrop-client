import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database from "better-sqlite3";

import type { Source, SourceObj, Item, ItemObj } from "../../types";

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

export const getSources = (): Source[] => {
  if (!db) {
    throw new Error("Database is not open");
  }

  // Select sources, along with all other data that needs to be displayed, in a single query
  const stmt = db.prepare(`
    SELECT
      s.uuid,
      s.data as source_data,
      COUNT(CASE WHEN json_extract(i.data, '$.kind') IN ('message', 'file') THEN 1 END) as readable_item_count,
      COUNT(CASE WHEN json_extract(i.data, '$.kind') IN ('message', 'file') AND json_extract(i.data, '$.is_read') = 1 THEN 1 END) as read_count,
      COUNT(CASE WHEN json_extract(i.data, '$.kind') = 'file' THEN 1 END) as file_count,
      COUNT(CASE WHEN json_extract(i.data, '$.kind') = 'message' THEN 1 END) as message_count,
      latest_message.plaintext as latest_message_plaintext
    FROM sources s
    LEFT JOIN items i ON s.uuid = json_extract(i.data, '$.source')
    LEFT JOIN (
      SELECT
        json_extract(data, '$.source') as source_uuid,
        plaintext,
        ROW_NUMBER() OVER (
          PARTITION BY json_extract(data, '$.source')
          ORDER BY json_extract(data, '$.last_updated') DESC
        ) as rn
      FROM items
      WHERE json_extract(data, '$.kind') = 'message'
    ) latest_message ON s.uuid = latest_message.source_uuid AND latest_message.rn = 1
    GROUP BY s.uuid, s.data, latest_message.plaintext
  `);

  const rows = stmt.all() as Array<{
    uuid: string;
    source_data: string;
    readable_item_count: number;
    read_count: number;
    file_count: number;
    message_count: number;
    latest_message_plaintext: string | null;
  }>;

  return rows.map((row) => {
    const data = JSON.parse(row.source_data);

    const isRead =
      row.readable_item_count > 0 && row.read_count === row.readable_item_count;

    const hasAttachment = row.file_count > 0;

    const showMessagePreview = row.message_count > 0;

    let messagePreview = "";
    if (showMessagePreview && row.latest_message_plaintext) {
      // Limit message preview to 200 characters
      messagePreview = row.latest_message_plaintext.slice(0, 200);
    }

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
      isRead,
      hasAttachment,
      showMessagePreview,
      messagePreview,
    };
  });
};

export const getItems = (sourceUuid: string): Item[] => {
  if (!db) {
    throw new Error("Database is not open");
  }

  const stmt = db.prepare(`
    SELECT uuid, data FROM items
    WHERE json_extract(data, '$.source') = ?;
  `);
  const rows = stmt.all(sourceUuid) as Array<{
    uuid: string;
    item_data: string;
  }>;

  return rows.map((row) => {
    const data = JSON.parse(row.item_data);
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
    };
  });
};
