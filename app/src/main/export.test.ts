import { describe, it, expect, beforeEach, afterEach } from "vitest";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";
import * as tar from "tar";
import {
  ArchiveExporter,
  PrintExportError,
  PrintState,
  PrintStateMachine,
  ExportState,
  ExportStateMachine,
} from "./export";
import { PrintStatus } from "../types";

// PrintStateMachine transitions
describe("PrintStateMachine", () => {
  it("should transition through valid states", () => {
    const fsm = new PrintStateMachine();
    expect(fsm.state).toBe(PrintState.Idle);

    fsm.transition({ action: "initiatePrint" });
    expect(fsm.state).toBe(PrintState.PrinterPreflight);

    fsm.transition({ action: "preflightSuccess" });
    expect(fsm.state).toBe(PrintState.PrinterPreflightComplete);

    fsm.transition({ action: "print" });
    expect(fsm.state).toBe(PrintState.Printing);

    fsm.transition({ action: "printSuccess" });
    expect(fsm.state).toBe(PrintState.Done);
  });

  it("should handle fail event from any state", () => {
    const fsm = new PrintStateMachine();
    fsm.transition({ action: "initiatePrint" });
    fsm.transition({ action: "fail", error: new Error("fail") });
    expect(fsm.state).toBe(PrintState.Error);
  });

  it("should throw on invalid transition", () => {
    const fsm = new PrintStateMachine();
    expect(() => fsm.transition({ action: "print" })).toThrow();
  });
});

// ExportStateMachine transitions
describe("ExportStateMachine", () => {
  it("should transition through valid states", () => {
    const fsm = new ExportStateMachine();
    expect(fsm.state).toBe(ExportState.Idle);

    fsm.transition({ action: "initiateExport" });
    expect(fsm.state).toBe(ExportState.ExportPreflight);

    fsm.transition({ action: "preflightSuccess" });
    expect(fsm.state).toBe(ExportState.ExportPreflightComplete);

    fsm.transition({ action: "export" });
    expect(fsm.state).toBe(ExportState.Exporting);

    fsm.transition({ action: "exportSuccess" });
    expect(fsm.state).toBe(ExportState.Done);
  });

  it("should handle fail event from any state", () => {
    const fsm = new ExportStateMachine();
    fsm.transition({ action: "initiateExport" });
    fsm.transition({ action: "fail", error: new Error("fail") });
    expect(fsm.state).toBe(ExportState.Error);
  });

  it("should throw on invalid transition", () => {
    const fsm = new ExportStateMachine();
    expect(() => fsm.transition({ action: "export" })).toThrow();
  });
});

// ArchiveExporter.parseStatus
describe("ArchiveExporter", () => {
  class TestExporter extends ArchiveExporter {}

  it("should parse known status from processStderr", () => {
    const exporter = new TestExporter();
    expect(exporter.parseStatus("some log\nPRINTER_SUCCESS")).toBe(
      PrintStatus.PRINT_SUCCESS,
    );
  });

  it("should throw PrintExportError for unknown status", () => {
    const exporter = new TestExporter();
    expect(() => exporter.parseStatus("foo\nBAR")).toThrow(PrintExportError);
  });

  it("should throw PrintExportError for empty output", () => {
    const exporter = new TestExporter();
    expect(() => exporter.parseStatus("")).toThrow(PrintExportError);
  });

  const tmpRoot = path.join(os.tmpdir(), "sd-export-test");

  function cleanupDir(dir: string) {
    if (fs.existsSync(dir)) {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }

  describe("ArchiveExporter.createArchive", () => {
    let archiveDir: string;

    beforeEach(() => {
      archiveDir = path.join(tmpRoot, "archive");
      fs.mkdirSync(archiveDir, {
        recursive: true,
      });
    });

    afterEach(() => {
      cleanupDir(archiveDir);
    });

    it("creates an archive with metadata.json only", async () => {
      const exporter = new ArchiveExporter();
      const archiveFilename = "test-archive.tar.gz";
      const metadata = { foo: "bar" };

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename,
        metadata,
      });

      expect(fs.existsSync(archivePath)).toBe(true);

      // Extract and check metadata.json
      const extractDir = path.join(archiveDir, "extract1");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });
      const metadataPath = path.join(extractDir, "metadata.json");
      expect(fs.existsSync(metadataPath)).toBe(true);
      const content = fs.readFileSync(metadataPath, "utf8");
      expect(JSON.parse(content)).toEqual(metadata);
      cleanupDir(extractDir);
    });

    it("creates an archive with metadata.json and one file", async () => {
      const exporter = new ArchiveExporter();
      const archiveFilename = "test-archive2.tar.gz";
      const metadata = { foo: "bar" };
      const fileContent = "hello world";
      const testFile = path.join(archiveDir, "file1.txt");
      fs.writeFileSync(testFile, fileContent);

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename,
        metadata,
        filepaths: [testFile],
      });

      expect(fs.existsSync(archivePath)).toBe(true);

      const extractDir = path.join(archiveDir, "extract2");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });
      expect(fs.existsSync(path.join(extractDir, "metadata.json"))).toBe(true);
      expect(
        fs.existsSync(path.join(extractDir, "export_data", "file1.txt")),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(extractDir, "export_data", "file1.txt"),
          "utf8",
        ),
      ).toBe(fileContent);
      cleanupDir(extractDir);
    });

    it("creates an archive with multiple files and correct structure", async () => {
      const exporter = new ArchiveExporter();
      const archiveFilename = "test-archive3.tar.gz";
      const metadata = { foo: "bar" };

      const parentDir = path.join(archiveDir, "parent");
      fs.mkdirSync(parentDir);
      const fileA = path.join(parentDir, "a.txt");
      const fileB = path.join(parentDir, "transcript.txt");
      fs.writeFileSync(fileA, "A");
      fs.writeFileSync(fileB, "B");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename,
        metadata,
        filepaths: [fileA, fileB],
      });

      expect(fs.existsSync(archivePath)).toBe(true);

      const extractDir = path.join(archiveDir, "extract3");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // transcript.txt should be under export_data/parent/transcript.txt
      expect(
        fs.existsSync(
          path.join(extractDir, "export_data", "parent", "transcript.txt"),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(extractDir, "export_data", "parent", "transcript.txt"),
          "utf8",
        ),
      ).toBe("B");

      expect(
        fs.existsSync(
          path.join(
            extractDir,
            "export_data",
            path.basename(archiveDir),
            path.basename(parentDir),
            "a.txt",
          ),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(
            extractDir,
            "export_data",
            path.basename(archiveDir),
            path.basename(parentDir),
            "a.txt",
          ),
          "utf8",
        ),
      ).toBe("A");
      cleanupDir(extractDir);
    });

    it("does not include missing files and removes metadata if all missing", async () => {
      const exporter = new ArchiveExporter();
      const archiveFilename = "test-archive4.tar.gz";
      const metadata = { foo: "bar" };
      const missingFile = path.join(archiveDir, "doesnotexist.txt");

      await expect(
        exporter.createArchive({
          archiveDir,
          archiveFilename,
          metadata,
          filepaths: [missingFile],
        }),
      ).rejects.toThrow();

      // Archive should not exist
      expect(fs.existsSync(path.join(archiveDir, archiveFilename))).toBe(false);
      // Metadata file should be cleaned up
      expect(fs.existsSync(path.join(archiveDir, "metadata.json"))).toBe(false);
    });
  });
});
