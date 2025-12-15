import {
  mkdtemp as mkdtempCb,
  chmod,
  constants,
  promises as fsPromises,
  rmSync,
} from "fs";
import * as os from "os";
import * as path from "path";
import { spawn, ChildProcess } from "child_process";
import { promisify } from "util";
import * as tar from "tar";
import {
  DeviceErrorStatus,
  DeviceStatus,
  ExportStatus,
  PrintStatus,
} from "../types";

const mkdtemp = promisify(mkdtempCb);
const chmodAsync = promisify(chmod);

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

export class ExportStateMachine implements StateMachine<
  ExportState,
  ExportEvent
> {
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
        // On USB device error, preflight may be re-run
        if (event.action === "initiateExport") {
          next = ExportState.ExportPreflight;
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
    // path on disk => path in archive
    const filesToAdd = new Map<string, string>();

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
            ArchiveExporter.DISK_EXPORT_DIR,
            grandParentName,
            parentName,
            filename,
          );
          if (filename === "transcript.txt") {
            arcname = path.join(
              ArchiveExporter.DISK_EXPORT_DIR,
              parentName,
              filename,
            );
          }
        }

        filesToAdd.set(filepath, arcname);
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

    // Create metadata.json content
    const metadataContent = JSON.stringify(metadata);
    const tempMetadataFile = path.join(
      archiveDir,
      `.${ArchiveExporter.METADATA_FILENAME}.tmp`,
    );

    try {
      // Write temporary metadata file
      await fsPromises.writeFile(tempMetadataFile, metadataContent, {
        encoding: "utf8",
      });

      await tar.create(
        {
          gzip: true,
          file: archivePath,
          portable: true,
          follow: false, // don't follow symlinks
          // Rewrite the path in the archive based on our mapping
          onWriteEntry(entry) {
            const targetPath = filesToAdd.get(entry.absolute);
            if (targetPath) {
              entry.path = targetPath;
            } else if (entry.absolute === tempMetadataFile) {
              entry.path = ArchiveExporter.METADATA_FILENAME;
            }
          },
        },
        [tempMetadataFile, ...filesToAdd.keys()],
      );
    } finally {
      // Cleanup temporary metadata file
      try {
        await fsPromises.unlink(tempMetadataFile);
      } catch (_e) {
        // Ignore errors if file doesn't exist
      }
    }
    return archivePath;
  }

  async runQrexecExport(archivePath: string): Promise<void> {
    return new Promise<void>((resolve, reject) => {
      this.processStderr = ""; // Reset buffer at start
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
      fsPromises
        .access(archivePath, constants.R_OK)
        .then(() => {
          this.process = spawn(qrexec, args, {
            stdio: ["ignore", "pipe", "pipe"],
          });

          if (!this.process) {
            console.log("Failed to spawn qrexec-client-vm");
            reject(new Error("Failed to spawn qrexec-client-vm"));
            return;
          }

          this.process.stderr?.on("data", (data) => {
            this.processStderr += data.toString();
          });

          this.process.on("error", (err) => {
            console.log("qrexec spawn error", err);
            reject(err);
          });

          this.process.on("close", (code, _signal) => {
            if (code === 0) {
              resolve();
            } else {
              reject(new Error(`Process exited with code ${code}`));
            }
          });
        })
        .catch((e) => {
          console.log("Archive path not accessible", e);
          reject(e);
        });
    });
  }

  // Parse stderr buffer of the child process for a final status line and return DeviceStatus.
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

  cleanupTmpdir() {
    if (this.tmpdir) {
      try {
        rmSync(this.tmpdir, { recursive: true, force: true });
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

      await this.runQrexecExport(archivePath);
      this._onComplete();
    } catch (err) {
      console.log("Error creating archive for printer preflight", err);
      this._onError();
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

      await this.runQrexecExport(archivePath);
      this._onComplete();
    } catch (err) {
      console.log("Print failed", err);
      this._onError();
    }
  }

  private _onError() {
    this.cleanupTmpdir();
    const errorMessage = this.processStderr;
    this.process = null;
    this.processStderr = "";
    this.fsm.transition({
      action: "fail",
      error: new PrintExportError(`Error: ${errorMessage}`),
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
          `Print status returned unexpected value ${e}`,
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
  }

  public async initiateExport(): Promise<DeviceStatus> {
    console.log("Beginning export preflight check");
    this.fsm.transition({ action: "initiateExport" });

    let status: DeviceStatus = DeviceErrorStatus.UNEXPECTED_RETURN_STATUS;

    try {
      this.tmpdir = await mkdtemp(path.join(os.tmpdir(), "sd-export-"));
      await chmodAsync(this.tmpdir, 0o700);

      const archivePath = await this.createArchive({
        archiveDir: this.tmpdir,
        archiveFilename: Exporter.USB_TEST_FILENAME,
        metadata: Exporter.USB_TEST_METADATA,
      });

      await this.runQrexecExport(archivePath);
      status = this._onComplete(true);
    } catch (err) {
      console.log("Export preflight check failed", err);
      this._onError();
    }
    return status;
  }

  public async export(
    filepaths: string[],
    passphrase: string | null,
  ): Promise<DeviceStatus> {
    let status: DeviceStatus;
    try {
      console.log(`Begin exporting ${filepaths.length} item(s)`);
      this.fsm.transition({ action: "export" });

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

      await this.runQrexecExport(archivePath);
      status = this._onComplete(false);
    } catch (err) {
      console.log("Export failed", err);
      this._onError();
      throw err;
    }
    return status;
  }

  private _onComplete(preflight: boolean): DeviceStatus {
    this.cleanupTmpdir();
    try {
      const status = this.parseStatus(this.processStderr);
      if (preflight) {
        this.fsm.transition({
          action: "preflightSuccess",
        });
        return status;
      }
      if (status === ExportStatus.SUCCESS_EXPORT) {
        this.fsm.transition({
          action: "exportSuccess",
        });
        return status;
      }
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(
          `Export failed with unexpected status: ${status}`,
        ),
      });
      return status;
    } catch (err) {
      this.fsm.transition({
        action: "fail",
        error: new PrintExportError(
          `Export status returned unexpected value ${err}`,
        ),
      });
      console.log("Export returned unexpected value", err);
      return DeviceErrorStatus.UNEXPECTED_RETURN_STATUS;
    } finally {
      this.process = null;
      this.processStderr = "";
    }
  }

  private _onError() {
    const errorMsg = this.processStderr;

    this.cleanupTmpdir();
    this.process = null;
    this.processStderr = "";
    this.fsm.transition({
      action: "fail",
      error: new PrintExportError(`Error: ${errorMsg}`),
    });
  }
}
