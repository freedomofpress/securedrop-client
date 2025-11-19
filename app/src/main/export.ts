import {
  mkdtemp as mkdtempCb,
  chmod,
  rm as rmCb,
  constants,
  promises as fsPromises,
} from "fs";
import * as os from "os";
import * as path from "path";
import { spawn, ChildProcess } from "child_process";
import { promisify } from "util";
import * as tar from "tar";

const mkdtemp = promisify(mkdtempCb);
const chmodAsync = promisify(chmod);
const rm = promisify(rmCb);

// All possible strings returned by the qrexec calls to sd-devices. These values come from
// `print/status.py` and `disk/status.py` in `securedrop-export`
// and must only be changed in coordination with changes released in that component.
export type DeviceStatus = ExportStatus | PrintStatus | DeviceErrorStatus;

export enum DeviceErrorStatus {
  // Misc errors
  CALLED_PROCESS_ERROR = "CALLED_PROCESS_ERROR",
  ERROR_USB_CONFIGURATION = "ERROR_USB_CONFIGURATION",
  UNEXPECTED_RETURN_STATUS = "UNEXPECTED_RETURN_STATUS",

  // Client-side error only
  ERROR_MISSING_FILES = "ERROR_MISSING_FILES", // All files meant for export are missing
}

export enum ExportStatus {
  // Success
  SUCCESS_EXPORT = "SUCCESS_EXPORT",

  // Error
  NO_DEVICE_DETECTED = "NO_DEVICE_DETECTED",
  INVALID_DEVICE_DETECTED = "INVALID_DEVICE_DETECTED", // Multi partitioned, not encrypted, etc
  MULTI_DEVICE_DETECTED = "MULTI_DEVICE_DETECTED", // Not currently supported
  UKNOWN_DEVICE_DETECTED = "UNKNOWN_DEVICE_DETECTED", // Badly-formatted USB or VeraCrypt/TC

  DEVICE_LOCKED = "DEVICE_LOCKED", // One valid device detected, and it's locked
  DEVICE_WRITABLE = "DEVICE_WRITABLE", // One valid device detected, and it's unlocked (and mounted)

  ERROR_UNLOCK_LUKS = "ERROR_UNLOCK_LUKS",
  ERROR_UNLOCK_GENERIC = "ERROR_UNLOCK_GENERIC",
  ERROR_MOUNT = "ERROR_MOUNT", // Unlocked but not mounted

  ERROR_EXPORT = "ERROR_EXPORT", // Could not write to disk

  // Export succeeds but drives were not properly closed
  ERROR_EXPORT_CLEANUP = "ERROR_EXPORT_CLEANUP",
  ERROR_UNMOUNT_VOLUME_BUSY = "ERROR_UNMOUNT_VOLUME_BUSY",

  DEVICE_ERROR = "DEVICE_ERROR", // Something went wrong while trying to check the device
}

export enum PrintStatus {
  // Success
  PRINT_PREFLIGHT_SUCCESS = "PRINTER_PREFLIGHT_SUCCESS",
  TEST_SUCCESS = "PRINTER_TEST_SUCCESS",
  PRINT_SUCCESS = "PRINTER_SUCCESS",

  // Error
  ERROR_PRINTER_NOT_FOUND = "ERROR_PRINTER_NOT_FOUND",
  ERROR_PRINT = "ERROR_PRINT",
  ERROR_UNPRINTABLE_TYPE = "ERROR_UNPRINTABLE_TYPE",
  ERROR_MIMETYPE_UNSUPPORTED = "ERROR_MIMETYPE_UNSUPPORTED",
  ERROR_MIMETYPE_DISCOVERY = "ERROR_MIMETYPE_DISCOVERY",
  ERROR_UNKNOWN = "ERROR_GENERIC", // Unknown printer error, backwards-compatible
}

export class PrintExportError extends Error {
  status?: DeviceStatus;
  constructor(message: string, status?: DeviceStatus) {
    super(message);
    this.name = "PrintExportError";
    this.status = status;
  }
}

export interface StateMachine<S, E> {
  state: S;
  transition(event: E): void;
  onError?(error: Error): void;
}

export const enum PrintState {
  Idle,
  PrinterPreflight,
  PrinterPreflightComplete,
  Printing,
  Done,
  Error,
}

export type PrintEvent =
  | { action: "initiatePrint" }
  | { action: "preflightSuccess" }
  | { action: "print" }
  | { action: "printSuccess" }
  | { action: "fail"; error: Error };

export class PrintStateMachine implements StateMachine<PrintState, PrintEvent> {
  state: PrintState = PrintState.Idle;
  onError?(error: Error): void;

  transition(event: PrintEvent) {
    const s = this.state;
    let next: PrintState | null = null;

    switch (s) {
      case PrintState.Idle:
      case PrintState.Done:
      case PrintState.Error:
        if (event.action === "initiatePrint") {
          next = PrintState.PrinterPreflight;
        }
        break;
      case PrintState.PrinterPreflight:
        if (event.action === "preflightSuccess") {
          next = PrintState.PrinterPreflightComplete;
        }
        break;
      case PrintState.PrinterPreflightComplete:
        if (event.action === "print") {
          next = PrintState.Printing;
        }
        break;
      case PrintState.Printing:
        if (event.action === "printSuccess") {
          next = PrintState.Done;
        }
        break;
    }
    if (event.action === "fail") {
      next = PrintState.Error;
      if (this.onError) {
        this.onError(event.error);
      }
    }

    if (next) {
      this.state = next;
    } else {
      throw new PrintExportError("invalid state transition");
    }
  }
}

export const enum ExportState {
  Idle,
  ExportPreflight,
  ExportPreflightComplete,
  Exporting,
  Done,
  Error,
}

export type ExportEvent =
  | { action: "initiateExport" }
  | { action: "preflightSuccess" }
  | { action: "export" }
  | { action: "exportSuccess" }
  | { action: "fail"; error: Error };

export class ExportStateMachine
  implements StateMachine<ExportState, ExportEvent>
{
  state: ExportState = ExportState.Idle;
  onError?(error: Error): void;

  transition(event: ExportEvent) {
    const s = this.state;
    let next: ExportState | null = null;

    switch (s) {
      case ExportState.Idle:
      case ExportState.Done:
      case ExportState.Error:
        if (event.action === "initiateExport") {
          next = ExportState.ExportPreflight;
        }
        break;
      case ExportState.ExportPreflight:
        if (event.action === "preflightSuccess") {
          next = ExportState.ExportPreflightComplete;
        }
        break;
      case ExportState.ExportPreflightComplete:
        if (event.action === "export") {
          next = ExportState.Exporting;
        }
        break;
      case ExportState.Exporting:
        if (event.action === "exportSuccess") {
          next = ExportState.Done;
        }
        break;
    }
    if (event.action === "fail") {
      next = ExportState.Error;
      if (this.onError) {
        this.onError(event.error);
      }
    }

    if (next) {
      this.state = next;
    } else {
      throw new PrintExportError("invalid state transition");
    }
  }
}

export class ArchiveExporter {
  private static readonly METADATA_FILENAME = "metadata.json";

  private static readonly DISK_EXPORT_DIR = "export_data";

  process: ChildProcess | null = null;
  processStderr: string = "";
  tmpdir: string | null = null;

  /**
   * Create an archive to be sent to the Export VM.
   *
   * @param archiveDir: The path to the directory in which to create the archive.
   * @param archiveFilename: The name of the archive file
   * @param metadata: Dictionary containing metadata to add to the archive
   * @param filepaths: Optional list of files to add to the archive.
   * @returns String path to newly-created archive file
   */
  async createArchive(opts: {
    archiveDir: string;
    archiveFilename: string;
    metadata: Record<string, unknown>;
    filepaths?: string[] | null;
  }): Promise<string> {
    const { archiveDir, archiveFilename, metadata } = opts;
    const filepaths = opts.filepaths ?? [];

    const archivePath = path.join(archiveDir, archiveFilename);

    let missingCount = 0;
    const filesToAdd: { src: string; tarPath: string }[] = [];

    const isOneOfMultipleFiles = filepaths.length > 1;

    for (const filepath of filepaths) {
      try {
        await fsPromises.access(filepath, constants.R_OK);
        const filename = path.basename(filepath);

        let arcname = path.join(ArchiveExporter.DISK_EXPORT_DIR, filename);
        if (isOneOfMultipleFiles) {
          const parentPath = path.dirname(filepath);
          const grandParentPath = path.dirname(parentPath);
          const parentName = path.basename(parentPath);
          const grandParentName = path.basename(grandParentPath);
          arcname = path.join(
            "export_data",
            grandParentName,
            parentName,
            filename,
          );
          if (filename === "transcript.txt") {
            arcname = path.join("export_data", parentName, filename);
          }
        }

        filesToAdd.push({ src: filepath, tarPath: arcname });
      } catch {
        missingCount += 1;
        console.debug(
          `'${filepath}' does not exist, and will not be included in archive`,
        );
      }
    }

    if (missingCount === filepaths.length && missingCount > 0) {
      throw new PrintExportError(
        "All files missing",
        DeviceErrorStatus.ERROR_MISSING_FILES,
      );
    }

    // Use tar.create to generate gzipped tarball.
    // Create staging directory with metadata and symlinks to files
    const tempDir = path.join(archiveDir, "staging");
    await fsPromises.mkdir(tempDir, { recursive: true });

    try {
      // Write metadata directly into staging directory
      await fsPromises.writeFile(
        path.join(tempDir, ArchiveExporter.METADATA_FILENAME),
        JSON.stringify(metadata),
        { encoding: "utf8" },
      );

      // For each file, create directories and symlink to original file
      for (const file of filesToAdd) {
        const destRelative = file.tarPath;
        const destFull = path.join(tempDir, destRelative);
        await fsPromises.mkdir(path.dirname(destFull), { recursive: true });
        await fsPromises.symlink(file.src, destFull);
      }

      // Create tar.gz from staging directory
      // The tar package will follow symlinks by default
      await tar.create(
        {
          gzip: true,
          file: archivePath,
          cwd: tempDir,
          portable: true,
        },
        ["."],
      );
    } finally {
      // Cleanup staging directory
      await rm(tempDir, { recursive: true, force: true });
    }
    return archivePath;
  }

  async runQrexecExport(
    archivePath: string,
    successCallback: () => void,
    errorCallback: () => void,
  ) {
    // args uses positional values, we intentionally avoid shell.
    const qrexec = "/usr/bin/qrexec-client-vm";
    const args = [
      "--",
      "sd-devices",
      "qubes.OpenInVM",
      "/usr/lib/qubes/qopen-in-vm",
      "--view-only",
      "--",
      archivePath,
    ];

    // Ensure file exists and is readable
    try {
      await fsPromises.access(archivePath, constants.R_OK);
    } catch (e) {
      console.log("Archive path not accessible", e);
      errorCallback();
      return;
    }

    this.process = spawn(qrexec, args, { stdio: ["ignore", "pipe", "pipe"] });

    if (!this.process) {
      console.log("Failed to spawn qrexec-client-vm");
      errorCallback();
      return;
    }

    this.process.stderr?.on("data", (data) => {
      this.processStderr += data.toString();
    });

    this.process.on("error", (err) => {
      console.log("qrexec spawn error", err);
      // process spawn failed
      this.cleanupTmpdir();
      errorCallback();
    });

    this.process.on("close", (code, _signal) => {
      if (code === 0) {
        successCallback();
      } else {
        errorCallback();
      }
    });
  }

  /// Parse stderr buffer of the child process for a final status line and return DeviceStatus.
  parseStatus(processStderr: string): DeviceStatus {
    const outputUntrusted = processStderr.trim();
    if (!outputUntrusted) {
      throw new PrintExportError(
        "Empty process output",
        DeviceErrorStatus.CALLED_PROCESS_ERROR,
      );
    }

    console.debug(`Parsing response from process: ${outputUntrusted}`);
    try {
      // final line is the status string
      const lines = outputUntrusted
        .split("\n")
        .map((l) => l.trim())
        .filter(Boolean);
      const last = lines.length > 0 ? lines[lines.length - 1] : "";
      if (!last)
        throw new PrintExportError(
          "No final line in sd-devices status response",
        );

      if (Object.values(ExportStatus).includes(last as ExportStatus)) {
        return last as ExportStatus;
      } else if (Object.values(PrintStatus).includes(last as PrintStatus)) {
        return last as PrintStatus;
      } else if (
        Object.values(DeviceErrorStatus).includes(last as DeviceErrorStatus)
      ) {
        return last as DeviceErrorStatus;
      } else {
        throw new PrintExportError(`Unknown status: ${last}`);
      }
    } catch (e) {
      throw new PrintExportError(
        `Unexpected return status ${e}`,
        DeviceErrorStatus.UNEXPECTED_RETURN_STATUS,
      );
    }
  }

  async cleanupTmpdir() {
    if (this.tmpdir) {
      try {
        await rm(this.tmpdir, { recursive: true, force: true });
      } catch (e) {
        console.log("Failed to cleanup tmpdir", e);
      } finally {
        this.tmpdir = null;
      }
    }
  }
}

export class Printer extends ArchiveExporter {
  private static readonly PRINTER_PREFLIGHT_FILENAME =
    "printer-preflight.sd-export";
  private static readonly PRINTER_PREFLIGHT_METADATA = {
    device: "printer-preflight",
  };

  private static readonly PRINT_FILENAME = "print_archive.sd-export";
  private static readonly PRINT_METADATA = { device: "printer" };

  private fsm: PrintStateMachine;

  constructor() {
    super();
    this.fsm = new PrintStateMachine();
    this.fsm.onError = this._onError;
  }

  // Initiate print and run preflight checks to make sure that Export VM is started
  public async initiatePrint(): Promise<void> {
    console.log("Initiating print, beginning printer preflight checks");
    this.fsm.transition({ action: "initiatePrint" });

    try {
      if (!this.tmpdir) {
        this.tmpdir = await mkdtemp(path.join(os.tmpdir(), "sd-export-"));
        await chmodAsync(this.tmpdir, 0o700);
      }

      const archivePath = await this.createArchive({
        archiveDir: this.tmpdir,
        archiveFilename: Printer.PRINTER_PREFLIGHT_FILENAME,
        metadata: Printer.PRINTER_PREFLIGHT_METADATA,
      });

      await this.runQrexecExport(
        archivePath,
        () => this._onComplete(),
        () => this._onError(),
      );
    } catch (err) {
      console.log("Error creating archive for printer preflight", err);
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(
          `Error creating archive for printer preflight: ${err}`,
        ),
      });
    }
  }

  public async print(filepaths: string[]): Promise<void> {
    console.log("Beginning print");
    this.fsm.transition({ action: "print" });

    try {
      if (!this.tmpdir) {
        this.tmpdir = await mkdtemp(path.join(os.tmpdir(), "sd-export-"));
        await chmodAsync(this.tmpdir, 0o700);
      }

      const archivePath = await this.createArchive({
        archiveDir: this.tmpdir,
        archiveFilename: Printer.PRINT_FILENAME,
        metadata: Printer.PRINT_METADATA,
        filepaths,
      });

      await this.runQrexecExport(
        archivePath,
        () => this._onComplete(),
        () => this._onError(),
      );
    } catch (err) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(`Print failed: ${err}`),
      });
    }
  }

  private _onError() {
    this.cleanupTmpdir();
    this.process = null;
    this.processStderr = "";
    this.fsm.transition({
      action: "fail",
      error: new PrintExportError(`Error: ${this.processStderr}`),
    });
  }

  private _onComplete() {
    this.cleanupTmpdir();
    try {
      const status = this.parseStatus(this.processStderr);
      if (status === PrintStatus.PRINT_PREFLIGHT_SUCCESS) {
        this.fsm.transition({ action: "preflightSuccess" });
      } else if (status === PrintStatus.PRINT_SUCCESS) {
        this.fsm.transition({ action: "printSuccess" });
      } else {
        this.fsm.transition({
          action: "fail",
          error: new PrintExportError(`Problem printing: ${status}`),
        });
      }
    } catch (e) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(
          `Export status returned unexpected value ${e}`,
        ),
      });
    } finally {
      this.process = null;
      this.processStderr = "";
    }
  }
}

export class Exporter extends ArchiveExporter {
  private static readonly USB_TEST_FILENAME = "usb-test.sd-export";
  private static readonly USB_TEST_METADATA = { device: "usb-test" };

  private static readonly DISK_FILENAME = "archive.sd-export";
  private static readonly DISK_METADATA = { device: "disk" };
  private static readonly DISK_ENCRYPTION_KEY_NAME = "encryption_key";

  private fsm: ExportStateMachine;

  constructor() {
    super();
    this.fsm = new ExportStateMachine();
    this.fsm.onError = this._onError;
  }

  public async runExportPreflightChecks(): Promise<void> {
    console.log("Beginning export preflight check");
    try {
      this.tmpdir = await mkdtemp(path.join(os.tmpdir(), "sd-export-"));
      await chmodAsync(this.tmpdir, 0o700);

      const archivePath = await this.createArchive({
        archiveDir: this.tmpdir,
        archiveFilename: Exporter.USB_TEST_FILENAME,
        metadata: Exporter.USB_TEST_METADATA,
      });

      await this.runQrexecExport(
        archivePath,
        () => this._onComplete(true),
        () => this._onError(),
      );
    } catch (err) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(`Export preflight check failed: ${err}`),
      });
    }
  }

  public async export(
    filepaths: string[],
    passphrase: string | null,
  ): Promise<void> {
    try {
      console.log(`Begin exporting ${filepaths.length} item(s)`);

      const metadata = { ...Exporter.DISK_METADATA } as Record<string, unknown>;
      if (passphrase) {
        metadata[Exporter.DISK_ENCRYPTION_KEY_NAME] = passphrase;
      }

      this.tmpdir = await mkdtemp(path.join(os.tmpdir(), "sd-export-"));
      await chmodAsync(this.tmpdir, 0o700);

      const archivePath = await this.createArchive({
        archiveDir: this.tmpdir,
        archiveFilename: Exporter.DISK_FILENAME,
        metadata,
        filepaths,
      });

      await this.runQrexecExport(
        archivePath,
        () => this._onComplete(false),
        () => this._onError(),
      );
    } catch (err) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(`Export failed: ${err}`),
      });
    }
  }

  private _onComplete(preflight: boolean) {
    this.cleanupTmpdir();
    try {
      const status = this.parseStatus(this.processStderr);
      if (status === ExportStatus.SUCCESS_EXPORT) {
        if (preflight) {
          this.fsm.transition({
            action: "preflightSuccess",
          });
        } else {
          this.fsm.transition({
            action: "exportSuccess",
          });
        }
      }
    } catch (err) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(
          `Export status returned unexpected value ${err}`,
        ),
      });
      console.log("Export preflight returned unexpected value", err);
    } finally {
      this.process = null;
      this.processStderr = "";
    }
  }

  private _onError() {
    this.cleanupTmpdir();
    this.process = null;
    this.processStderr = "";
    this.fsm.transition({
      action: "fail",
      error: new PrintExportError(`Error: ${this.processStderr}`),
    });
  }
}
