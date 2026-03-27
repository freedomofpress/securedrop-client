import { describe, expect, it, beforeAll, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { DB } from "./index";
import { Crypto } from "../crypto";
import { setUmask } from "../umask";

describe("Database Component Tests", () => {
  const testHomeDir = path.join(os.tmpdir(), "test-home");
  const testDbDir = path.join(testHomeDir, ".config", "SecureDrop");
  const testDbPath = path.join(testDbDir, "db.sqlite");
  const originalHomedir = os.homedir;
  let originalUmask: number;
  let db: DB;
  let crypto: Crypto;

  beforeAll(() => {
    (Crypto as any).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  });

  beforeEach(() => {
    // Set umask for secure file permissions
    originalUmask = process.umask();
    setUmask();

    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
    os.homedir = () => testHomeDir;
  });

  afterEach(() => {
    if (db) {
      db.close();
    }
    process.umask(originalUmask);
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  it("should create database with correct setup", () => {
    db = new DB(crypto);

    expect(db).toBeDefined();
    expect(fs.existsSync(testDbPath)).toBe(true);
    expect(db["db"]!.pragma("journal_mode", { simple: true })).toBe("wal");
    expect(db["db"]!.pragma("secure_delete", { simple: true })).toBe(1);
    expect(db["db"]!.pragma("auto_vacuum", { simple: true })).toBe(1);
  });

  it("should handle database closure", () => {
    db = new DB(crypto);
    expect(db).toBeDefined();

    db.close();
    expect(() => db.close()).not.toThrow();
  });

  it("should create valid database file", () => {
    db = new DB(crypto);
    const stats = fs.statSync(testDbPath);
    expect(stats.isFile()).toBe(true);
    expect(stats.size).toBeGreaterThan(0);

    // Verify file has correct permissions (0o600 - owner read/write only)
    const permissions = stats.mode & 0o777;
    expect(permissions).toBe(0o600);

    // Verify database directory has correct permissions (0o700)
    const dirStats = fs.statSync(testDbDir);
    const dirPermissions = dirStats.mode & 0o777;
    expect(dirPermissions).toBe(0o700);
  });

  describe("items_kind_immutable trigger", () => {
    it("allows TOFU initial write", () => {
      db = new DB(crypto);
      const rawDb = db["db"]!;

      rawDb
        .prepare("INSERT INTO items (uuid, data) VALUES (?, NULL)")
        .run("item-tofu");

      expect(() =>
        rawDb.prepare("UPDATE items SET data = ? WHERE uuid = ?").run(
          JSON.stringify({
            kind: "message",
            uuid: "item-tofu",
            source: "s",
            size: 0,
            is_read: false,
            seen_by: [],
            interaction_count: 0,
          }),
          "item-tofu",
        ),
      ).not.toThrow();
    });

    it("rejects a change of kind from 'message' to 'file'", () => {
      db = new DB(crypto);
      const rawDb = db["db"]!;

      rawDb.prepare("INSERT INTO items (uuid, data) VALUES (?, ?)").run(
        "item-msg",
        JSON.stringify({
          kind: "message",
          uuid: "item-msg",
          source: "s",
          size: 0,
          is_read: false,
          seen_by: [],
          interaction_count: 0,
        }),
      );

      expect(() =>
        rawDb.prepare("UPDATE items SET data = ? WHERE uuid = ?").run(
          JSON.stringify({
            kind: "file",
            uuid: "item-msg",
            source: "s",
            size: 0,
            is_read: false,
            seen_by: [],
            interaction_count: 0,
          }),
          "item-msg",
        ),
      ).toThrow("items.kind is immutable");
    });
  });
});
