import { describe, expect, it, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { DB } from "./index";

describe("Database Component Tests", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home");
  const testDbDir = path.join(testHomeDir, ".config", "SecureDrop");
  const testDbPath = path.join(testDbDir, "db.sqlite");
  const originalHomedir = os.homedir;
  let db: DB;

  beforeEach(() => {
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
  });

  afterEach(() => {
    if (db) {
      db.close();
    }
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  it("should create database with correct setup", () => {
    db = new DB();

    expect(db).toBeDefined();
    expect(fs.existsSync(testDbPath)).toBe(true);
    expect(db["db"]!.pragma("journal_mode", { simple: true })).toBe("wal");
  });

  it("should handle database closure", () => {
    db = new DB();
    expect(db).toBeDefined();

    db.close();
    expect(() => db.close()).not.toThrow();
  });

  it("should create valid database file", () => {
    db = new DB();
    const stats = fs.statSync(testDbPath);
    expect(stats.isFile()).toBe(true);
    expect(stats.size).toBeGreaterThan(0);
  });

});
