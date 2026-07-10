import fs from "fs";
import os from "os";
import path from "path";

import * as tar from "tar";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import {
  DeviceErrorStatus,
  ItemMetadata,
  PrintStatus,
  SourceMetadata,
} from "../types";
import { Crypto } from "./crypto";
import { Datastore } from "./datastore";
import { ArchiveExporter, Exporter, EXPORT_QUBE, Printer } from "./export";
import { prepareSourceExport } from "./source-export";
import { Storage } from "./storage";

const OLD_MESSAGE = "SENTINEL_OLD_MESSAGE_IN_ALL_HISTORY_TRANSCRIPT";
const OLD_FILE = "SENTINEL_OLD_FILE_IN_ALL_HISTORY_EXPORT";
const NEW_DURING_EXPORT = "SENTINEL_NEW_FILE_AFTER_TRANSCRIPT_SNAPSHOT";

function sourceMetadata(uuid: string): SourceMetadata {
  return {
    uuid,
    journalist_designation: "export source",
    is_starred: false,
    is_seen: false,
    has_attachment: true,
    last_updated: "2026-07-08T00:00:00Z",
    public_key: "unused",
    fingerprint: "unused",
  };
}

function itemMetadata(
  uuid: string,
  interactionCount: number,
  kind: "message" | "reply" | "file",
): ItemMetadata {
  if (kind === "reply") {
    return {
      uuid,
      source: "source-1",
      kind,
      size: 1,
      journalist_uuid: "journalist-1",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: interactionCount,
    };
  }
  return {
    uuid,
    source: "source-1",
    kind,
    size: 1,
    is_read: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

function seedItems(db: Datastore, storage: Storage, itemCount: number): void {
  const items: Record<string, ItemMetadata> = {};
  for (
    let interactionCount = 1;
    interactionCount <= itemCount;
    interactionCount += 1
  ) {
    const uuid = `item-${interactionCount.toString().padStart(3, "0")}`;
    let kind: "message" | "reply" | "file" = "message";
    if ([2, 60, 120, 121].includes(interactionCount)) {
      kind = "file";
    } else if (interactionCount % 5 === 0) {
      kind = "reply";
    }
    items[uuid] = itemMetadata(uuid, interactionCount, kind);
  }
  db.updateItems(items);

  for (const item of Object.values(items)) {
    if (item.kind === "file") {
      continue;
    }
    const plaintext =
      item.interaction_count === 1
        ? OLD_MESSAGE
        : `item ${item.interaction_count}`;
    db.completePlaintextItem(item.uuid, plaintext);
  }

  const oldFile = items["item-002"];
  if (oldFile) {
    completeFile(db, storage, oldFile, OLD_FILE);
  }
  const newerFile = items["item-060"];
  if (newerFile) {
    completeFile(db, storage, newerFile, "newer file");
  }
  if (items["item-121"]) {
    db.completeFileItem("item-121", "/missing/item-121/payload.txt", 1);
  }
}

function completeFile(
  db: Datastore,
  storage: Storage,
  metadata: ItemMetadata,
  content: string,
): string {
  const filename = storage.itemDirectory(metadata).join("payload.txt");
  fs.writeFileSync(filename, content, "utf8");
  db.completeFileItem(metadata.uuid, filename, Buffer.byteLength(content));
  return filename;
}

async function extractArchive(
  archivePath: string,
  root: string,
): Promise<string> {
  const extractDir = path.join(root, `extract-${path.basename(archivePath)}`);
  fs.mkdirSync(extractDir, { recursive: true });
  await tar.x({ file: archivePath, cwd: extractDir });
  return extractDir;
}

describe("source-wide archival workflows", () => {
  const originalHomedir = os.homedir;
  let homeDir: string;
  let db: Datastore;
  let storage: Storage;

  beforeEach(() => {
    homeDir = fs.mkdtempSync(
      path.join(fs.realpathSync(os.tmpdir()), "source-export-"),
    );
    os.homedir = () => homeDir;
    storage = new Storage();
    db = new Datastore({} as Crypto, storage);
    db.updateSources({ "source-1": sourceMetadata("source-1") });
  });

  afterEach(() => {
    vi.restoreAllMocks();
    if (db) {
      db.close();
    }
    os.homedir = originalHomedir;
    fs.rmSync(homeDir, { recursive: true, force: true });
  });

  it("exports all 201 projected items from one snapshot", async () => {
    seedItems(db, storage, 201);

    const getJournalists = db.getJournalists.bind(db);
    vi.spyOn(db, "getJournalists").mockImplementation(() => {
      const metadata = itemMetadata("item-202", 202, "file");
      db.updateItems({ "item-202": metadata });
      completeFile(db, storage, metadata, NEW_DURING_EXPORT);
      return getJournalists();
    });

    const prepared = await prepareSourceExport("source-1", db);
    expect(prepared.filepaths).toHaveLength(3);
    expect(prepared.sourceName).toBe("export source");
    expect(fs.readFileSync(prepared.filepaths[0]!, "utf8")).toContain(
      OLD_MESSAGE,
    );
    expect(prepared.filepaths.some((file) => file.includes("item-202"))).toBe(
      false,
    );
    expect(db.getItem("item-202")).not.toBeNull();

    const archiveDir = path.join(homeDir, "archive");
    fs.mkdirSync(archiveDir);
    const archivePath = await new ArchiveExporter(EXPORT_QUBE).createArchive({
      archiveDir,
      archiveFilename: "source-export.sd-export",
      metadata: { device: "disk" },
      filepaths: prepared.filepaths,
      sourceName: prepared.sourceName,
    });
    const extracted = await extractArchive(archivePath, homeDir);
    const exportRoot = path.join(extracted, "export_data", "export source");

    expect(fs.readdirSync(exportRoot).sort()).toEqual([
      "item-002-payload.txt",
      "item-060-payload.txt",
      "source-1-transcript.txt",
    ]);
    expect(
      fs.readFileSync(path.join(exportRoot, "item-002-payload.txt"), "utf8"),
    ).toBe(OLD_FILE);
    expect(
      fs.readFileSync(path.join(exportRoot, "source-1-transcript.txt"), "utf8"),
    ).toContain(OLD_MESSAGE);
    expect(
      fs.readdirSync(exportRoot).some((name) => name.includes("item-202")),
    ).toBe(false);
    expect(
      fs.readdirSync(exportRoot).some((name) => name.includes("item-120")),
    ).toBe(false);
    expect(
      fs.readdirSync(exportRoot).some((name) => name.includes("item-121")),
    ).toBe(false);
  });

  it("keeps the normal 100-item transcript complete", async () => {
    seedItems(db, storage, 100);
    const prepared = await prepareSourceExport("source-1", db);
    const transcript = fs.readFileSync(prepared.filepaths[0]!, "utf8");

    expect(transcript).toContain(OLD_MESSAGE);
    expect(transcript).toContain("item 100");
    expect(db.getSourceWithItems("source-1").hasMoreHistoricalItems).toBe(
      false,
    );
  });

  it("prints the all-history transcript through the production archive workflow", async () => {
    seedItems(db, storage, 101);
    const prepared = await prepareSourceExport("source-1", db);

    class CapturingPrinter extends Printer {
      printedTranscript = "";

      override async runQrexecExport(archivePath: string): Promise<void> {
        const extracted = await extractArchive(archivePath, homeDir);
        if (archivePath.includes("printer-preflight")) {
          this.processStderr = PrintStatus.PRINT_PREFLIGHT_SUCCESS;
          return;
        }
        const transcriptPath = path.join(
          extracted,
          "export_data",
          "source-1-transcript.txt",
        );
        this.printedTranscript = fs.readFileSync(transcriptPath, "utf8");
        this.processStderr = PrintStatus.PRINT_SUCCESS;
      }
    }

    const printer = new CapturingPrinter();
    expect(await printer.initiatePrint()).toBe(
      PrintStatus.PRINT_PREFLIGHT_SUCCESS,
    );
    expect(await printer.print([prepared.filepaths[0]!])).toBe(
      PrintStatus.PRINT_SUCCESS,
    );
    expect(printer.printedTranscript).toContain(OLD_MESSAGE);
    expect(printer.tmpdir).toBeNull();
  });

  it("cleans export and print temporary archives after transfer failures", async () => {
    seedItems(db, storage, 1);
    const prepared = await prepareSourceExport("source-1", db);

    class FailingExporter extends Exporter {
      failedArchiveDir: string | null = null;

      override async runQrexecExport(archivePath: string): Promise<void> {
        this.failedArchiveDir = path.dirname(archivePath);
        throw new Error("export transfer failed");
      }
    }
    const exporter = new FailingExporter();
    await expect(
      exporter.export(prepared.filepaths, null, prepared.sourceName, true),
    ).rejects.toThrow("export transfer failed");
    expect(exporter.tmpdir).toBeNull();
    if (!exporter.failedArchiveDir) {
      throw new Error("export did not reach the transfer boundary");
    }
    expect(fs.existsSync(exporter.failedArchiveDir)).toBe(false);

    class FailingPrinter extends Printer {
      calls = 0;
      failedArchiveDir: string | null = null;

      override async runQrexecExport(archivePath: string): Promise<void> {
        this.calls += 1;
        if (this.calls === 1) {
          this.processStderr = PrintStatus.PRINT_PREFLIGHT_SUCCESS;
          return;
        }
        this.failedArchiveDir = path.dirname(archivePath);
        throw new Error("print transfer failed");
      }
    }
    const printer = new FailingPrinter();
    expect(await printer.initiatePrint()).toBe(
      PrintStatus.PRINT_PREFLIGHT_SUCCESS,
    );
    expect(await printer.print([prepared.filepaths[0]!])).toBe(
      DeviceErrorStatus.UNEXPECTED_RETURN_STATUS,
    );
    expect(printer.tmpdir).toBeNull();
    if (!printer.failedArchiveDir) {
      throw new Error("print did not reach the transfer boundary");
    }
    expect(fs.existsSync(printer.failedArchiveDir)).toBe(false);
  });
});
