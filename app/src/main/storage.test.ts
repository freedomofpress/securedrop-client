import { describe, expect, it, beforeEach, afterEach } from "vitest";
import fs from "fs";
import path from "path";
import os from "os";
import { PathBuilder, Storage } from "./storage";
import { ItemMetadata } from "../types";
import { ItemFetchTask } from "./fetch/queue";

describe("PathBuilder", () => {
  describe("constructor", () => {
    it("should create PathBuilder with valid directory path", () => {
      const builder = new PathBuilder("/tmp/");
      expect(builder.path).toBe("/tmp/");
      const builder2 = new PathBuilder("/tmp/test/nested/");
      expect(builder2.path).toBe("/tmp/test/nested/");
    });

    it("should throw errors on bad input", () => {
      expect(() => new PathBuilder("tmp/")).toThrow(
        "Root path must be absolute and start with /",
      );
      expect(() => new PathBuilder("/tmp")).toThrow(
        "Root path must be a directory and end with /",
      );
      expect(() => new PathBuilder("relative/path/")).toThrow(
        "Root path must be absolute and start with /",
      );
      expect(() => new PathBuilder("../etc/")).toThrow(
        "Root path must be absolute and start with /",
      );
      expect(() => new PathBuilder("./tmp/")).toThrow(
        "Root path must be absolute and start with /",
      );
    });
  });

  describe("validate", () => {
    let builder: PathBuilder;

    beforeEach(() => {
      builder = new PathBuilder("/tmp/");
    });

    it("should accept valid path component", () => {
      expect(() => builder.validate("valid")).not.toThrow();
      expect(() => builder.validate("valid-name")).not.toThrow();
      expect(() => builder.validate("valid_name")).not.toThrow();
      expect(() => builder.validate("123")).not.toThrow();
    });

    it("should reject bad input", () => {
      expect(() => builder.validate("invalid/path")).toThrow(
        "Invalid path component: invalid/path",
      );
      expect(() => builder.validate("..")).toThrow(
        "Invalid path component: ..",
      );
      expect(() => builder.validate(".")).toThrow("Invalid path component: .");
      expect(() => builder.validate("")).toThrow("Invalid path component: ");
      expect(() => builder.validate("path/to/file")).toThrow(
        "Invalid path component: path/to/file",
      );
    });
  });

  describe("getSubBuilder", () => {
    let builder: PathBuilder;

    beforeEach(() => {
      builder = new PathBuilder("/tmp/");
    });

    it("should create sub-builder with single component", () => {
      const sub = builder.getSubBuilder("test");
      expect(sub.path).toBe("/tmp/test/");
      expect(sub).toBeInstanceOf(PathBuilder);
    });

    it("should create sub-builder with multiple components", () => {
      const sub = builder.getSubBuilder("foo", "bar", "baz");
      expect(sub.path).toBe("/tmp/foo/bar/baz/");
    });

    it("should chain sub-builders", () => {
      const sub1 = builder.getSubBuilder("first");
      const sub2 = sub1.getSubBuilder("second");
      const sub3 = sub2.getSubBuilder("third");

      expect(sub1.path).toBe("/tmp/first/");
      expect(sub2.path).toBe("/tmp/first/second/");
      expect(sub3.path).toBe("/tmp/first/second/third/");
    });

    it("should reject bad input", () => {
      expect(() => builder.getSubBuilder("..")).toThrow(
        "Invalid path component: ..",
      );
      expect(() => builder.getSubBuilder("foo/bar")).toThrow(
        "Invalid path component: foo/bar",
      );
      expect(() => builder.getSubBuilder("")).toThrow(
        "Invalid path component: ",
      );
      expect(() => builder.getSubBuilder("valid", "..", "also-valid")).toThrow(
        "Invalid path component: ..",
      );
    });
  });

  describe("join", () => {
    let tempDir: string;
    let builder: PathBuilder;

    beforeEach(() => {
      tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "pathbuilder-test-"));
      builder = new PathBuilder(tempDir + "/");
    });

    afterEach(() => {
      if (fs.existsSync(tempDir)) {
        fs.rmSync(tempDir, { recursive: true, force: true });
      }
    });

    it("should join path components", () => {
      const result = builder.join("file.txt");
      expect(result).toBe(`${tempDir}/file.txt`);
      const result2 = builder.join("foo", "bar", "file.txt");
      expect(result2).toBe(`${tempDir}/foo/bar/file.txt`);
    });

    it("should reject bad input", () => {
      expect(() => builder.join("..")).toThrow("Invalid path component: ..");
      expect(() => builder.join("foo/bar")).toThrow(
        "Invalid path component: foo/bar",
      );
    });

    it("should detect symlink escape attempts", () => {
      // Create a symlink pointing outside the root directory
      const outsideDir = fs.mkdtempSync(
        path.join(os.tmpdir(), "pathbuilder-outside-"),
      );
      const symlinkPath = path.join(tempDir, "escape");

      try {
        fs.symlinkSync(outsideDir, symlinkPath);

        expect(() => builder.join("escape")).toThrow(
          `Path ${tempDir}/escape escapes root ${tempDir}/`,
        );
      } finally {
        if (fs.existsSync(symlinkPath)) {
          fs.unlinkSync(symlinkPath);
        }
        if (fs.existsSync(outsideDir)) {
          fs.rmSync(outsideDir, { recursive: true, force: true });
        }
      }
    });

    // this test will fail on macOS, because tmpdir() is /var, but it's
    // a symlink to /private/var, which escapes the root and fails
    it.skipIf(os.platform() === "darwin")(
      "should allow valid symlinks within root",
      () => {
        // Create target and symlink within the root
        const targetDir = path.join(tempDir, "target");
        const symlinkPath = path.join(tempDir, "link");

        fs.mkdirSync(targetDir);
        fs.symlinkSync(targetDir, symlinkPath);

        try {
          const result = builder.join("link");
          expect(result).toBe(`${tempDir}/link`);
        } finally {
          fs.unlinkSync(symlinkPath);
          fs.rmdirSync(targetDir);
        }
      },
    );

    it("should not check symlinks for non-existent paths", () => {
      // This should not throw even though the path doesn't exist
      const result = builder.join("nonexistent", "file.txt");
      expect(result).toBe(`${tempDir}/nonexistent/file.txt`);
    });
  });
});

describe("Storage", () => {
  let storage: Storage;
  let originalHomedir: () => string;
  let testHomeDir: string;

  beforeEach(() => {
    // Create test home directory
    testHomeDir = fs.mkdtempSync(path.join(os.tmpdir(), "storage-test-home-"));
    originalHomedir = os.homedir;
    os.homedir = () => testHomeDir;

    storage = new Storage();
  });

  afterEach(() => {
    os.homedir = originalHomedir;
    if (fs.existsSync(testHomeDir)) {
      fs.rmSync(testHomeDir, { recursive: true, force: true });
    }
  });

  describe("constructor", () => {
    it("should initialize persistent storage path", () => {
      expect(storage["persistent"].path).toBe(
        `${testHomeDir}/.config/SecureDrop/files/`,
      );
    });

    it("should initialize tmp storage path", () => {
      expect(storage["tmp"].path).toBe(os.tmpdir() + "/");
    });
  });

  describe("downloadFilePath", () => {
    it("should construct download file path with all components", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid-123",
        source: "source-uuid-456",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 1,
      };
      const item: ItemFetchTask = {
        id: "item-uuid-123",
      };

      const result = storage.downloadFilePath(metadata, item);
      expect(result).toBe(
        `${os.tmpdir()}/download/source-uuid-456/item-uuid-123/encrypted.gpg`,
      );
    });

    it("should reject malicious source ID with path traversal", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid",
        source: "../../../etc",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 4,
      };
      const item: ItemFetchTask = {
        id: "item-uuid",
      };

      expect(() => storage.downloadFilePath(metadata, item)).toThrow(
        "Invalid path component: ../../../etc",
      );
    });

    it("should reject malicious item ID with slash", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid",
        source: "source-uuid",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 5,
      };
      const item: ItemFetchTask = {
        id: "../../secret",
      };

      expect(() => storage.downloadFilePath(metadata, item)).toThrow(
        "Invalid path component: ../../secret",
      );
    });
  });

  describe("sourceDirectory", () => {
    it("should return PathBuilder for source directory", () => {
      const result = storage.sourceDirectory("source-123");
      expect(result).toBeInstanceOf(PathBuilder);
      expect(result.path).toBe(
        `${testHomeDir}/.config/SecureDrop/files/source-123/`,
      );
    });

    it("should reject path traversal in source ID", () => {
      expect(() => storage.sourceDirectory("..")).toThrow(
        "Invalid path component: ..",
      );
      expect(() => storage.sourceDirectory("foo/bar")).toThrow(
        "Invalid path component: foo/bar",
      );
    });
  });

  describe("itemDirectory", () => {
    it("should return PathBuilder for item directory", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid-789",
        source: "source-uuid-456",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 6,
      };

      const result = storage.itemDirectory(metadata);
      expect(result).toBeInstanceOf(PathBuilder);
      expect(result.path).toBe(
        `${testHomeDir}/.config/SecureDrop/files/source-uuid-456/item-uuid-789/`,
      );
    });

    it("should reject malicious source ID in metadata", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid",
        source: "../../../etc",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 9,
      };

      expect(() => storage.itemDirectory(metadata)).toThrow(
        "Invalid path component: ../../../etc",
      );
    });

    it("should reject malicious item UUID in metadata", () => {
      const metadata: ItemMetadata = {
        uuid: "../../passwd",
        source: "source-uuid",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 10,
      };

      expect(() => storage.itemDirectory(metadata)).toThrow(
        "Invalid path component: ../../passwd",
      );
    });

    it("should allow using join on item directory", () => {
      const metadata: ItemMetadata = {
        uuid: "item-uuid",
        source: "source-uuid",
        kind: "file",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 11,
      };

      const itemDir = storage.itemDirectory(metadata);
      const filePath = itemDir.join("document.pdf");

      expect(filePath).toBe(
        `${testHomeDir}/.config/SecureDrop/files/source-uuid/item-uuid/document.pdf`,
      );
    });
  });

  describe("createTempDir", () => {
    const createdDirs: string[] = [];

    afterEach(() => {
      // Clean up any created temp directories
      for (const dir of createdDirs) {
        if (fs.existsSync(dir)) {
          fs.rmSync(dir, { recursive: true, force: true });
        }
      }
      createdDirs.length = 0;
    });

    it("should create temporary directory with prefix", () => {
      const result = storage.createTempDir("test-prefix-");
      createdDirs.push(result.path);

      expect(result).toBeInstanceOf(PathBuilder);
      expect(fs.existsSync(result.path)).toBe(true);
      expect(result.path).toContain("test-prefix-");
      expect(result.path.startsWith(os.tmpdir())).toBe(true);
    });

    it("should create unique directories for each call", () => {
      const result1 = storage.createTempDir("unique-");
      const result2 = storage.createTempDir("unique-");

      createdDirs.push(result1.path, result2.path);

      expect(result1.path).not.toBe(result2.path);
      expect(fs.existsSync(result1.path)).toBe(true);
      expect(fs.existsSync(result2.path)).toBe(true);
    });

    it("should reject path traversal in prefix", () => {
      expect(() => storage.createTempDir("../evil-")).toThrow(
        "Invalid path component",
      );
    });
  });
});
