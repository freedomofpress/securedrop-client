import { describe, expect, it, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { openDatabase, closeDatabase } from "./index";

describe("Database Integration Tests", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home");
  const testDbDir = path.join(testHomeDir, ".config", "SecureDrop");
  const testDbPath = path.join(testDbDir, "db.sqlite");
  const originalHomedir = os.homedir;

  beforeEach(() => {
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
  });

  afterEach(() => {
    closeDatabase();
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  it("should create database with correct setup", () => {
    const db = openDatabase();

    expect(db).toBeDefined();
    expect(fs.existsSync(testDbPath)).toBe(true);
    expect(db.pragma("journal_mode", { simple: true })).toBe("wal");
  });

  it("should return singleton instance and handle closure", () => {
    const db1 = openDatabase();
    const db2 = openDatabase();
    expect(db1).toBe(db2);

    closeDatabase();
    const newDb = openDatabase();
    expect(newDb).not.toBe(db1);

    closeDatabase();
    expect(() => closeDatabase()).not.toThrow();
  });

  it("should create valid database file", () => {
    openDatabase();
    const stats = fs.statSync(testDbPath);
    expect(stats.isFile()).toBe(true);
    expect(stats.size).toBeGreaterThan(0);
  });
});
