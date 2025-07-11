import fs from "fs";
import os from "os";
import path from "path";
import { execSync } from "child_process";
import Database from "better-sqlite3";

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
  console.log(`__dirname: ${__dirname}`);
  console.log(`process.mainModule?.filename: ${process.mainModule?.filename}`);
  console.log(`process.env.NODE_ENV: ${process.env.NODE_ENV}`);
  const isPackaged =
    process.mainModule?.filename.includes("app.asar") ||
    process.env.NODE_ENV === "production";

  let dbmatePath: string;
  let migrationsDir: string;

  if (isPackaged) {
    // In packaged app, use paths relative to the app resources
    const appPath = process.resourcesPath || path.dirname(process.execPath);
    dbmatePath = path.join(appPath, "app", "node_modules", ".bin", "dbmate");
    migrationsDir = path.join(
      appPath,
      "app",
      "src",
      "main",
      "database",
      "migrations",
    );
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
