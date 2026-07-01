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
  Exporter,
  ExportState,
  ExportStateMachine,
  EXPORT_QUBE,
} from "./export";
import { ExportStatus, PrintStatus } from "../types";

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
  class TestExporter extends ArchiveExporter {
    constructor() {
      super(EXPORT_QUBE);
    }
  }

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
      const exporter = new ArchiveExporter(EXPORT_QUBE);
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
      const exporter = new ArchiveExporter(EXPORT_QUBE);
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
        fs.existsSync(
          path.join(extractDir, "export_data", "archive-file1.txt"),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(extractDir, "export_data", "archive-file1.txt"),
          "utf8",
        ),
      ).toBe(fileContent);
      cleanupDir(extractDir);
    });

    it("creates an archive with multiple files and correct structure", async () => {
      const exporter = new ArchiveExporter(EXPORT_QUBE);
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

      // Without sourceName, files go directly under export_data/ with parent prefix
      expect(
        fs.existsSync(
          path.join(extractDir, "export_data", "parent-transcript.txt"),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(extractDir, "export_data", "parent-transcript.txt"),
          "utf8",
        ),
      ).toBe("B");

      expect(
        fs.existsSync(path.join(extractDir, "export_data", "parent-a.txt")),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(extractDir, "export_data", "parent-a.txt"),
          "utf8",
        ),
      ).toBe("A");
      cleanupDir(extractDir);
    });

    it("creates an archive with sourceName and files under source directory", async () => {
      const exporter = new ArchiveExporter(EXPORT_QUBE);
      const archiveFilename = "test-archive5.tar.gz";
      const metadata = { foo: "bar" };

      const parentDir = path.join(archiveDir, "parent");
      fs.mkdirSync(parentDir, { recursive: true });
      const fileA = path.join(parentDir, "a.txt");
      const fileB = path.join(parentDir, "transcript.txt");
      fs.writeFileSync(fileA, "A");
      fs.writeFileSync(fileB, "B");

      const archivePath = await exporter.createArchive({
        archiveDir,
        archiveFilename,
        metadata,
        filepaths: [fileA, fileB],
        sourceName: "jovial_seahorse",
      });

      expect(fs.existsSync(archivePath)).toBe(true);

      const extractDir = path.join(archiveDir, "extract5");
      fs.mkdirSync(extractDir);
      await tar.x({ file: archivePath, cwd: extractDir });

      // With sourceName, files go under export_data/<sourceName>/ with parent prefix
      expect(
        fs.existsSync(
          path.join(
            extractDir,
            "export_data",
            "jovial_seahorse",
            "parent-transcript.txt",
          ),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(
            extractDir,
            "export_data",
            "jovial_seahorse",
            "parent-transcript.txt",
          ),
          "utf8",
        ),
      ).toBe("B");

      expect(
        fs.existsSync(
          path.join(
            extractDir,
            "export_data",
            "jovial_seahorse",
            "parent-a.txt",
          ),
        ),
      ).toBe(true);
      expect(
        fs.readFileSync(
          path.join(
            extractDir,
            "export_data",
            "jovial_seahorse",
            "parent-a.txt",
          ),
          "utf8",
        ),
      ).toBe("A");
      cleanupDir(extractDir);
    });

    it("does not include missing files and removes metadata if all missing", async () => {
      const exporter = new ArchiveExporter(EXPORT_QUBE);
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

// Exports are handled by a single Exporter instance, holding the export FSM state.
// If concurrent export operations ran, they could mutate that shared singleton
// state, resulting in invalid state transitions.
//
// Export operations should acquire a lock, enforcing that only one export is
// in progress at a given time.
describe("Exporter guards against concurrent export operations", () => {
  // Mock the qrexec process so the test can control when the export operation finishes
  function mockQrexec() {
    let release!: () => void;
    const promise = new Promise<void>((resolve) => {
      release = resolve;
    });
    return { promise, release };
  }

  // Test Exporter that keeps ALL production logic but replaces the real qrexec
  // transfer with a gated stub, so we can observe shared state mid-transfer.
  class HarnessExporter extends Exporter {
    qrexec = mockQrexec();
    obs: Record<string, unknown> = {};

    // Observe private FSM state for test
    fsmState(): ExportState {
      // @ts-expect-error -- fsm is private; we only read it for observation.
      return this.fsm.state as ExportState;
    }

    async runQrexecExport(archivePath: string): Promise<void> {
      const fakeProcess = { kill: () => {}, killed: false };
      this.process = fakeProcess as unknown as typeof this.process;

      this.obs.archiveExistsAtTransferStart = fs.existsSync(archivePath);

      // Transfer is now "in flight". Block until the test releases us.
      await this.qrexec.promise;

      this.obs.archiveExistsAtTransferEnd = fs.existsSync(archivePath);
      this.obs.processHandleAtTransferEnd = this.process;
    }
  }

  it("rejects a second export without corrupting the in-flight export", async () => {
    const src = fs.mkdtempSync(path.join(os.tmpdir(), "sd-race-src-"));
    const file = path.join(src, "secret.txt");
    fs.writeFileSync(file, "in-flight payload");

    const exporter = new HarnessExporter();

    // Export A: whistleflow=true takes the exportDirect path: Idle -> Exporting ---
    const a = exporter.export([file], null, undefined, true);

    // Let Export A reach the gated transfer (archive created, process spawned).
    await new Promise((r) => setTimeout(r, 50));

    const beforeB = exporter.fsmState();
    expect(beforeB).toBe(ExportState.Exporting);

    // Export B: a concurrent export against the same instance ---
    let bError: unknown = null;
    try {
      await exporter.export([file], null, undefined, false);
    } catch (e) {
      bError = e;
    }

    const afterB = exporter.fsmState();

    // Release Export A's transfer and let it settle.
    exporter.qrexec.release();
    const aResult = await a.then(
      (v) => ({ status: "fulfilled" as const, value: v }),
      (e) => ({ status: "rejected" as const, reason: e }),
    );

    // B must be rejected by the single-flight guard
    expect(bError).not.toBeNull();
    expect(String(bError)).toContain("already in progress");
    // but has not hit an invalid state transition
    expect(String(bError)).not.toContain("invalid state transition");

    // In-flight Export A is untouched
    // Archive still present throughout the transfer.
    expect(exporter.obs.archiveExistsAtTransferStart).toBe(true);
    expect(exporter.obs.archiveExistsAtTransferEnd).toBe(true);
    // Process handle still owned by A during the transfer.
    expect(exporter.obs.processHandleAtTransferEnd).not.toBeNull();
    // FSM stayed in Exporting
    expect(afterB).toBe(ExportState.Exporting);

    // A completes successfully
    expect(aResult.status).toBe("fulfilled");
    expect(aResult.status === "fulfilled" && aResult.value).toBe(
      ExportStatus.SUCCESS_EXPORT,
    );
  });

  it("allows a fresh export after the previous one completes (lock is released)", async () => {
    const src = fs.mkdtempSync(path.join(os.tmpdir(), "sd-race-src2-"));
    const file = path.join(src, "secret.txt");
    fs.writeFileSync(file, "payload");

    const exporter = new HarnessExporter();

    // First export: release immediately so it completes.
    exporter.qrexec.release();
    const first = await exporter.export([file], null, undefined, true);
    expect(first).toBe(ExportStatus.SUCCESS_EXPORT);

    // A subsequent, non-overlapping export must be allowed (lock was released).
    exporter.qrexec = mockQrexec();
    exporter.qrexec.release();
    const second = await exporter.export([file], null, undefined, true);
    expect(second).toBe(ExportStatus.SUCCESS_EXPORT);
  });
});
