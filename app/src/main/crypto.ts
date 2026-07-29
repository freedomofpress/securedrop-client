import {
  spawn,
  type ChildProcessWithoutNullStreams,
  type SpawnOptionsWithoutStdio,
} from "child_process";
import { createGunzip } from "zlib";
import { Transform, TransformCallback } from "stream";
import { pipeline } from "stream/promises";

import * as openpgp from "openpgp";
import * as fs from "fs";
import * as path from "path";
import { PathBuilder, Storage, UnsafePathComponent } from "./storage";
import { ms } from "../types";

// Allow 3 minutes for decryption, which might need to wait for sd-gpg to start
const SHELL_TIMEOUT = 180_000 as ms;
export const MAX_DECRYPTED_BYTES = 500 * 1024 * 1024;
export const MAX_GPG_STDERR_BYTES = 64 * 1024;
const GZIP_HEADER_READ_BYTES = 1024;
const GZIP_TRAILER_BYTES = 8;
const GZIP_FIXED_HEADER_BYTES = 10;
const GZIP_EXTRA_FLAG = 4;
const GZIP_FILENAME_FLAG = 8;
const GZIP_MAGIC = Buffer.from([0x1f, 0x8b]);

// The server's 500 MiB Apache/Flask cap covers the entire source request, so
// the uploaded stream is smaller than this plaintext limit. It stores that
// stream in one gzip member. Bound its deflate representation with zlib's
// compressBound formula, then allow the header bytes this client can parse and
// the fixed gzip trailer without assuming a separate filename limit.
export const MAX_DECRYPTED_GZIP_BYTES =
  MAX_DECRYPTED_BYTES +
  Math.floor(MAX_DECRYPTED_BYTES / 4096) +
  Math.floor(MAX_DECRYPTED_BYTES / 16384) +
  Math.floor(MAX_DECRYPTED_BYTES / 33554432) +
  13 +
  GZIP_HEADER_READ_BYTES +
  GZIP_TRAILER_BYTES;

class DecryptedSizeLimitError extends Error {
  constructor(stage: string, maxBytes = MAX_DECRYPTED_BYTES) {
    super(`${stage} exceeds the ${maxBytes}-byte limit`);
    this.name = "DecryptedSizeLimitError";
  }
}

class BoundedBufferCollector {
  private readonly chunks: Buffer[] = [];
  private bytesSeen = 0;

  constructor(private readonly maxBytes: number) {}

  append(chunk: Buffer): boolean {
    const remaining = this.maxBytes - this.bytesSeen;
    if (remaining > 0) {
      this.chunks.push(Buffer.from(chunk.subarray(0, remaining)));
      this.bytesSeen += Math.min(chunk.length, remaining);
    }
    return chunk.length <= remaining;
  }

  toString(): string {
    return Buffer.concat(this.chunks, this.bytesSeen).toString("utf8");
  }
}

class Utf8MessageCollector {
  private readonly decoder = new TextDecoder("utf-8", {
    fatal: true,
    ignoreBOM: true,
  });
  private readonly chunks: string[] = [];
  private bytesSeen = 0;

  append(chunk: Buffer): void {
    this.bytesSeen += chunk.length;
    if (this.bytesSeen > MAX_DECRYPTED_BYTES) {
      throw new DecryptedSizeLimitError("Decrypted message");
    }
    const decoded = this.decoder.decode(chunk, { stream: true });
    if (decoded) {
      this.chunks.push(decoded);
    }
  }

  finish(): string {
    const decoded = this.decoder.decode();
    if (decoded) {
      this.chunks.push(decoded);
    }
    return this.chunks.join("");
  }
}

class ByteLimitTransform extends Transform {
  private bytesSeen = 0;

  constructor(
    private readonly stage: string,
    private readonly maxBytes: number,
  ) {
    super();
  }

  override _transform(
    chunk: Buffer,
    _encoding: BufferEncoding,
    callback: TransformCallback,
  ): void {
    this.bytesSeen += chunk.length;
    if (this.bytesSeen > this.maxBytes) {
      callback(
        new Error(`${this.stage} exceeds the ${this.maxBytes}-byte limit`),
      );
      return;
    }
    callback(null, chunk);
  }
}

export function createDecryptedByteLimit(
  stage: string,
  maxBytes = MAX_DECRYPTED_BYTES,
): Transform {
  return new ByteLimitTransform(stage, maxBytes);
}

export interface CryptoConfig {
  isQubes: boolean;
  gpgHomedir?: string;
  qubesGpgDomain?: string;
  submissionKeyFingerprint: string;
}

// Strictly validate GPG's stderr to prevent injection attacks (gpg.fail) where it exits with a zero status code.
// We need to handle:
// 1) File decryption, encrypted to just the journalist key
// 2) Message decryption, encrypted to just the journalist key
// 3) Reply decryption, encrypted to both the source and journalist keys. In this case, the source key
//    may or may not be imported in to the keyring (the legacy client imported source keys).

// These are hardcoded English, which should be fine since there are no other locales in sd-gpg.
// File decryption (1 recipient) or message decryption (1 recipient) or reply decryption with source key in keyring (2 recipients)
// GPG versions differ in how they describe the key: older versions use "4096-bit RSA key", newer use "rsa4096 key".
const GPG_STDERR_KNOWN_KEY =
  /^(gpg: encrypted with (?:4096-bit RSA|rsa4096) key, ID [0-9A-Fa-f]+, created \d{4}-\d{2}-\d{2}\n\s+"[^"]*"\n){1,2}$/;
// Reply decryption: source key not in keyring (anonymous) + journalist key (known).
// GPG may output the anonymous key before or after the known key depending on the version.
const GPG_STDERR_ANONYMOUS_THEN_KNOWN =
  /^(gpg: encrypted with RSA key, ID [0-9A-Fa-f]+\n)(gpg: encrypted with (?:4096-bit RSA|rsa4096) key, ID [0-9A-Fa-f]+, created \d{4}-\d{2}-\d{2}\n\s+"[^"]*"\n)$/;
const GPG_STDERR_KNOWN_THEN_ANONYMOUS =
  /^(gpg: encrypted with (?:4096-bit RSA|rsa4096) key, ID [0-9A-Fa-f]+, created \d{4}-\d{2}-\d{2}\n\s+"[^"]*"\n)(gpg: encrypted with RSA key, ID [0-9A-Fa-f]+\n)$/;
const GPG_STDERR_LOCKFILE_DISAPPEARED = /^(?:gpg: lockfile disappeared\n)+/;

function isExpectedGpgStderr(stderr: string): boolean {
  const normalized = stderr.trimEnd() + "\n";
  const withoutLockfileDiagnostic = normalized.replace(
    GPG_STDERR_LOCKFILE_DISAPPEARED,
    "",
  );
  return (
    GPG_STDERR_KNOWN_KEY.test(withoutLockfileDiagnostic) ||
    GPG_STDERR_ANONYMOUS_THEN_KNOWN.test(withoutLockfileDiagnostic) ||
    GPG_STDERR_KNOWN_THEN_ANONYMOUS.test(withoutLockfileDiagnostic)
  );
}

export class CryptoError extends Error {
  constructor(
    message: string,
    public readonly cause?: Error,
  ) {
    super(message);
    this.name = "CryptoError";
  }
}

type GpgScope = "message" | "file";

function asError(error: unknown): Error {
  return error instanceof Error ? error : new Error(String(error));
}

function createAbortError(): Error {
  const error = new Error("Decryption was cancelled");
  error.name = "AbortError";
  return error;
}

function throwIfAborted(signal?: AbortSignal): void {
  if (signal?.aborted) {
    throw createAbortError();
  }
}

function isCancellation(error: unknown): boolean {
  return error instanceof Error && error.name === "AbortError";
}

async function settleAbortable<T>(
  operation: Promise<T>,
  signal?: AbortSignal,
): Promise<T> {
  try {
    const result = await operation;
    throwIfAborted(signal);
    return result;
  } catch (error) {
    if (signal?.aborted) {
      throw createAbortError();
    }
    throw error;
  }
}

function cleanupFailure(message: string, error: unknown): CryptoError {
  return new CryptoError(message, asError(error));
}

async function syncFile(filePath: string, signal?: AbortSignal): Promise<void> {
  throwIfAborted(signal);
  const file = await fs.promises.open(filePath, "r");
  try {
    throwIfAborted(signal);
    await settleAbortable(file.sync(), signal);
  } finally {
    await file.close();
  }
  throwIfAborted(signal);
}

async function removeDirectoryIfExists(directoryPath: string): Promise<void> {
  try {
    await fs.promises.rm(directoryPath, { force: true, recursive: true });
  } catch {
    try {
      fs.rmSync(directoryPath, { force: true, recursive: true });
    } catch (syncError) {
      throw cleanupFailure(
        "Failed to remove temporary decrypted files",
        syncError,
      );
    }
  }
}

async function publishFileWithoutReplace(
  temporaryOutputPath: string,
  finalOutputPath: string,
  signal?: AbortSignal,
): Promise<void> {
  throwIfAborted(signal);
  try {
    await fs.promises.link(temporaryOutputPath, finalOutputPath);
  } catch (error) {
    if (signal?.aborted) {
      throw createAbortError();
    }
    throw error;
  }
}

function startGpgTimeout(callback: () => void): NodeJS.Timeout {
  const timeout = setTimeout(callback, SHELL_TIMEOUT);
  timeout.unref();
  return timeout;
}

function clearGpgTimeout(timeout: NodeJS.Timeout | null): void {
  if (timeout) {
    clearTimeout(timeout);
  }
}

function stopGpgProcess(
  process: ChildProcessWithoutNullStreams,
  terminate: boolean,
): void {
  if (terminate) {
    process.kill();
  }
  process.stdin.destroy?.();
  process.stdout.destroy?.();
  process.stderr.destroy?.();
}

function messageOutputError(error: unknown): CryptoError {
  const cause = asError(error);
  const message =
    cause instanceof DecryptedSizeLimitError
      ? cause.message
      : "Decrypted message is not valid UTF-8";
  return new CryptoError(message, cause);
}

function gpgStderrLimitError(): CryptoError {
  return new CryptoError(
    `GPG stderr exceeds the ${MAX_GPG_STDERR_BYTES}-byte limit`,
  );
}

function gpgInputError(error: Error): CryptoError {
  return new CryptoError("Failed to write encrypted content to GPG", error);
}

function gpgFileInputError(error: Error): CryptoError {
  return new CryptoError("GPG file input stream failed", error);
}

function gpgOutputWriteError(error: unknown): CryptoError {
  return new CryptoError(
    "Failed to write decrypted GPG output",
    asError(error),
  );
}

function writeGpgInput(
  process: ChildProcessWithoutNullStreams,
  encryptedContent: Buffer,
  fail: (error: Error) => void,
): void {
  try {
    process.stdin.write(encryptedContent);
    process.stdin.end();
  } catch (error) {
    fail(gpgInputError(asError(error)));
  }
}

function gpgCompletionError(
  scope: GpgScope,
  code: number | null,
  signal: NodeJS.Signals | null,
  stderr: string,
): Error | null {
  if (signal) {
    return new Error(`Process terminated with signal ${signal}`);
  }
  const prefix = scope === "file" ? "GPG file decryption" : "GPG decryption";
  if (code !== 0) {
    return new CryptoError(`${prefix} failed (exit code ${code}): ${stderr}`);
  }
  if (stderr.trim() && !isExpectedGpgStderr(stderr)) {
    const label = scope === "file" ? "GPG file decryption" : "GPG decryption";
    return new CryptoError(
      `${label} emitted stderr: ${JSON.stringify(stderr.trim())}`,
    );
  }
  return null;
}

function gpgSpawnError(scope: GpgScope, error: Error): CryptoError {
  const context = scope === "file" ? " for file decryption" : "";
  return new CryptoError(
    `Failed to start GPG process${context}: ${error.message}`,
    error,
  );
}

function spawnGpgProcess(
  command: string[],
  options: SpawnOptionsWithoutStdio,
  scope: GpgScope,
): ChildProcessWithoutNullStreams {
  try {
    return spawn(command[0], command.slice(1), options);
  } catch (error) {
    throw gpgSpawnError(scope, asError(error));
  }
}

function fileCloseError(
  code: number | null,
  signal: NodeJS.Signals | null,
  stderr: string,
): Error | null {
  if (code === 0 && !signal) {
    return null;
  }
  return (
    gpgCompletionError("file", code, signal, stderr) ??
    new CryptoError("GPG file decryption failed")
  );
}

interface MessageProcessHandlers {
  abort: () => void;
  close: (code: number | null, signal: NodeJS.Signals | null) => void;
  processError: (error: Error) => void;
  stderr: (chunk: Buffer) => void;
  stderrError: (error: Error) => void;
  stdinError: (error: Error) => void;
  stdout: (chunk: Buffer) => void;
  stdoutError: (error: Error) => void;
}

function registerMessageProcessHandlers(
  process: ChildProcessWithoutNullStreams,
  signal: AbortSignal | undefined,
  handlers: MessageProcessHandlers,
): void {
  process.stdin.on?.("error", handlers.stdinError);
  process.stdout.on("error", handlers.stdoutError);
  process.stderr.on("error", handlers.stderrError);
  process.stdout.on("data", handlers.stdout);
  process.stderr.on("data", handlers.stderr);
  process.on("error", handlers.processError);
  process.on("close", handlers.close);
  signal?.addEventListener("abort", handlers.abort, { once: true });
}

interface FileProcessHandlers {
  abort: () => void;
  close: (code: number | null, signal: NodeJS.Signals | null) => void;
  pipelineError: (error: unknown) => void;
  pipelineSuccess: () => void;
  processError: (error: Error) => void;
  stderr: (chunk: Buffer) => void;
  stderrError: (error: Error) => void;
  stdinError: (error: Error) => void;
}

function registerFileProcessHandlers(
  process: ChildProcessWithoutNullStreams,
  outputPipeline: Promise<void>,
  signal: AbortSignal | undefined,
  handlers: FileProcessHandlers,
): void {
  process.stdin.on("error", handlers.stdinError);
  process.stderr.on("error", handlers.stderrError);
  process.stderr.on("data", handlers.stderr);
  process.on("error", handlers.processError);
  process.on("close", handlers.close);
  signal?.addEventListener("abort", handlers.abort, { once: true });
  outputPipeline.then(handlers.pipelineSuccess, handlers.pipelineError);
}

class GpgMessageCollectorRunner {
  private readonly diagnostics = new BoundedBufferCollector(
    MAX_GPG_STDERR_BYTES,
  );
  private readonly plaintext = new Utf8MessageCollector();
  private reject!: (reason?: unknown) => void;
  private resolve!: (value: string) => void;
  private settled = false;
  private timeout: NodeJS.Timeout | null = null;

  constructor(
    private readonly process: ChildProcessWithoutNullStreams,
    private readonly encryptedContent: Buffer,
    private readonly signal?: AbortSignal,
  ) {}

  run(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.resolve = resolve;
      this.reject = reject;
      this.registerHandlers();
      this.timeout = startGpgTimeout(() => this.onTimeout());
      this.startInput();
    });
  }

  private finish(
    error: Error | null,
    result?: string,
    terminate = false,
  ): void {
    if (this.settled) {
      return;
    }
    this.settled = true;
    clearGpgTimeout(this.timeout);
    this.signal?.removeEventListener("abort", this.onAbort);
    stopGpgProcess(this.process, terminate);
    if (error) {
      this.reject(error);
      return;
    }
    this.resolve(result ?? "");
  }

  private failStreamRead(description: string, error: Error): void {
    this.finish(
      new CryptoError(`Failed to read GPG ${description}`, error),
      undefined,
      true,
    );
  }

  private finishPlaintext(): void {
    try {
      this.finish(null, this.plaintext.finish());
    } catch (decodeError) {
      this.finish(messageOutputError(decodeError));
    }
  }

  private onAbort = (): void => {
    this.finish(createAbortError(), undefined, true);
  };

  private onClose = (
    code: number | null,
    exitSignal: NodeJS.Signals | null,
  ): void => {
    if (this.settled) {
      return;
    }
    const error = gpgCompletionError(
      "message",
      code,
      exitSignal,
      this.diagnostics.toString(),
    );
    if (error) {
      this.finish(error);
      return;
    }
    this.finishPlaintext();
  };

  private onStderr = (chunk: Buffer): void => {
    if (!this.diagnostics.append(chunk)) {
      this.finish(gpgStderrLimitError(), undefined, true);
    }
  };

  private onStdout = (chunk: Buffer): void => {
    try {
      this.plaintext.append(chunk);
    } catch (error) {
      this.finish(messageOutputError(error), undefined, true);
    }
  };

  private onTimeout(): void {
    this.finish(
      new CryptoError("GPG message decryption timed out"),
      undefined,
      true,
    );
  }

  private registerHandlers(): void {
    registerMessageProcessHandlers(this.process, this.signal, {
      abort: this.onAbort,
      close: this.onClose,
      processError: (error) =>
        this.finish(gpgSpawnError("message", error), undefined, true),
      stderr: this.onStderr,
      stderrError: (error) => this.failStreamRead("diagnostics", error),
      stdinError: (error) => this.finish(gpgInputError(error), undefined, true),
      stdout: this.onStdout,
      stdoutError: (error) => this.failStreamRead("message output", error),
    });
  }

  private startInput(): void {
    if (this.signal?.aborted) {
      this.onAbort();
      return;
    }
    writeGpgInput(this.process, this.encryptedContent, (error) =>
      this.finish(error, undefined, true),
    );
  }
}

function collectGpgMessage(
  process: ChildProcessWithoutNullStreams,
  encryptedContent: Buffer,
  signal?: AbortSignal,
): Promise<string> {
  return new GpgMessageCollectorRunner(process, encryptedContent, signal).run();
}

class GpgFileOutputWriter {
  private closeResult: [number | null, NodeJS.Signals | null] | null = null;
  private readonly diagnostics = new BoundedBufferCollector(
    MAX_GPG_STDERR_BYTES,
  );
  private readonly output: fs.WriteStream;
  private outputPipeline!: Promise<void>;
  private pipelineDone = false;
  private pipelineError: Error | null = null;
  private reject!: (reason?: unknown) => void;
  private resolve!: () => void;
  private settled = false;
  private timeout: NodeJS.Timeout | null = null;

  constructor(
    private readonly process: ChildProcessWithoutNullStreams,
    outputPath: string,
    private readonly signal?: AbortSignal,
  ) {
    this.output = fs.createWriteStream(outputPath, { flags: "wx" });
  }

  run(): Promise<void> {
    return new Promise((resolve, reject) => {
      this.resolve = resolve;
      this.reject = reject;
      this.startPipeline();
      this.registerHandlers();
      this.timeout = startGpgTimeout(() => this.onTimeout());
      if (this.signal?.aborted) {
        this.onAbort();
      }
    });
  }

  private complete(): void {
    if (this.settled || !this.pipelineDone || !this.closeResult) {
      return;
    }
    const error = gpgCompletionError(
      "file",
      this.closeResult[0],
      this.closeResult[1],
      this.diagnostics.toString(),
    );
    if (error) {
      this.fail(error, false);
      return;
    }
    this.settled = true;
    clearGpgTimeout(this.timeout);
    this.signal?.removeEventListener("abort", this.onAbort);
    stopGpgProcess(this.process, false);
    this.resolve();
  }

  private fail(error: Error, terminate = true): void {
    if (this.settled) {
      return;
    }
    this.settled = true;
    clearGpgTimeout(this.timeout);
    this.signal?.removeEventListener("abort", this.onAbort);
    stopGpgProcess(this.process, terminate);
    this.output.destroy();
    void this.outputPipeline
      .catch(() => undefined)
      .then(() => this.reject(error));
  }

  private onAbort = (): void => {
    this.fail(createAbortError());
  };

  private onClose = (
    code: number | null,
    exitSignal: NodeJS.Signals | null,
  ): void => {
    if (this.pipelineError) {
      this.fail(this.pipelineError, false);
      return;
    }
    const error = fileCloseError(code, exitSignal, this.diagnostics.toString());
    if (error) {
      this.fail(error, false);
      return;
    }
    this.closeResult = [code, exitSignal];
    this.complete();
  };

  private onPipelineError = (error: unknown): void => {
    if (this.settled) {
      return;
    }
    this.pipelineError = gpgOutputWriteError(error);
    stopGpgProcess(this.process, true);
    if (this.closeResult) {
      this.fail(this.pipelineError, false);
    }
  };

  private onStderr = (chunk: Buffer): void => {
    if (!this.diagnostics.append(chunk)) {
      this.fail(gpgStderrLimitError());
    }
  };

  private onTimeout(): void {
    this.fail(new CryptoError("GPG file decryption timed out"));
  }

  private registerHandlers(): void {
    registerFileProcessHandlers(
      this.process,
      this.outputPipeline,
      this.signal,
      {
        abort: this.onAbort,
        close: this.onClose,
        pipelineError: this.onPipelineError,
        pipelineSuccess: () => {
          this.pipelineDone = true;
          this.complete();
        },
        processError: (error) => this.fail(gpgSpawnError("file", error)),
        stderr: this.onStderr,
        stderrError: (error) =>
          this.fail(new CryptoError("Failed to read GPG diagnostics", error)),
        stdinError: (error) => this.fail(gpgFileInputError(error)),
      },
    );
  }

  private startPipeline(): void {
    this.outputPipeline = pipeline(
      this.process.stdout,
      createDecryptedByteLimit("GPG-decrypted file", MAX_DECRYPTED_GZIP_BYTES),
      this.output,
      { signal: this.signal },
    );
  }
}

function writeGpgOutputToFile(
  process: ChildProcessWithoutNullStreams,
  outputPath: string,
  signal?: AbortSignal,
): Promise<void> {
  return new GpgFileOutputWriter(process, outputPath, signal).run();
}

function gzipFilenameOffset(data: Buffer): number {
  if ((data[3] & GZIP_EXTRA_FLAG) === 0) {
    return GZIP_FIXED_HEADER_BYTES;
  }
  if (GZIP_FIXED_HEADER_BYTES + 2 > data.length) {
    throw new Error("Incomplete gzip header");
  }
  return (
    GZIP_FIXED_HEADER_BYTES + 2 + data.readUInt16LE(GZIP_FIXED_HEADER_BYTES)
  );
}

function decodeGzipFilename(
  data: Buffer,
  filenameStart: number,
): UnsafePathComponent | null {
  const filenameEnd = data.indexOf(0, filenameStart);
  if (filenameEnd < 0) {
    throw new Error("Filename in gzip header not null-terminated");
  }
  const filename = data.subarray(filenameStart, filenameEnd).toString("utf8");
  return filename.trim() ? new UnsafePathComponent(filename) : null;
}

export class Crypto {
  private static instance: Crypto;
  private isQubes: boolean;
  private gpgHomedir?: string;
  private qubesGpgDomain?: string;
  private submissionKeyFingerprint: string;
  private submissionKey?: string;

  private constructor(config: CryptoConfig) {
    this.isQubes = config.isQubes;
    this.gpgHomedir = config.gpgHomedir;
    this.qubesGpgDomain = config.qubesGpgDomain;
    this.submissionKeyFingerprint = config.submissionKeyFingerprint;
  }

  /**
   * Initialize global crypto configuration (must be called before getInstance)
   */
  public static initialize(config: CryptoConfig): Crypto {
    if (Crypto.instance) {
      throw new Error(
        "Crypto already initialized: cannot initialize twice. Call initialize() before getInstance().",
      );
    }

    Crypto.instance = new Crypto(config);
    return Crypto.instance;
  }

  /**
   * Get singleton instance of Crypto
   */
  public static getInstance(): Crypto | null {
    if (!Crypto.instance) {
      return null;
    }
    return Crypto.instance;
  }

  /**
   * Get the base GPG command based on environment (Qubes vs dev)
   */
  private getGpgCommand(): string[] {
    if (this.isQubes) {
      return ["qubes-gpg-client", "--trust-model", "always"];
    } else {
      const cmd = ["gpg", "--trust-model", "always"];
      if (this.gpgHomedir) {
        cmd.push("--homedir", this.gpgHomedir);
      }
      return cmd;
    }
  }

  private getSpawnOptions(): SpawnOptionsWithoutStdio {
    let env: NodeJS.ProcessEnv;
    if (this.isQubes && this.qubesGpgDomain) {
      env = { ...process.env, QUBES_GPG_DOMAIN: this.qubesGpgDomain };
    } else {
      env = process.env;
    }
    return {
      env: env,
    };
  }

  /**
   * Lazily get the public part of the submission key
   */
  async getSubmissionKey(): Promise<string> {
    if (!this.submissionKey) {
      this.submissionKey = await this.exportSubmissionKey();
    }
    return this.submissionKey;
  }

  /**
   * Internal method to export the public part of the submission key
   * from sd-gpg by using qubes-split-gpg
   */
  async exportSubmissionKey(): Promise<string> {
    const cmd = this.getGpgCommand();
    cmd.push("--export", "--armor", this.submissionKeyFingerprint);

    return new Promise((resolve, reject) => {
      const process = spawn(cmd[0], cmd.slice(1), this.getSpawnOptions());
      let stdout = "";
      let stderr = "";
      const timeout = setTimeout(() => process.kill(), SHELL_TIMEOUT);
      timeout.unref();

      process.stdout.on("data", (data) => {
        stdout += data.toString();
      });

      process.stderr.on("data", (data) => {
        stderr += data.toString();
      });

      process.on("error", (err) => {
        clearTimeout(timeout);
        reject(err);
      });

      process.on("close", (code, signal) => {
        clearTimeout(timeout);
        if (signal) {
          reject(new Error(`Process terminated with signal ${signal}`));
        } else if (code !== 0) {
          reject(
            new Error(`Process exited with non-zero code ${code}: ${stderr}`),
          );
        } else if (stderr.trim()) {
          reject(
            // n.b. use JSON.stringify() to sanitize the error since it's not what we expect
            // and could be the result of some sort of injection attack
            new Error(
              `Received stderr when exporting ${this.submissionKeyFingerprint}: ${JSON.stringify(stderr)}`,
            ),
          );
        } else if (!stdout.trim()) {
          reject(
            new Error(
              `Failed to export key ${this.submissionKeyFingerprint}: Key not found or export returned empty result`,
            ),
          );
        } else {
          resolve(stdout);
        }
      });
    });
  }

  /**
   * Decrypt a message from encrypted buffer content
   * Messages are not gzipped, so no decompression is needed (unlike files)
   * @param encryptedContent - The encrypted message content
   * @returns Promise<string> - The decrypted plaintext
   */
  async decryptMessage(
    encryptedContent: Buffer,
    signal?: AbortSignal,
  ): Promise<string> {
    if (signal?.aborted) {
      throw createAbortError();
    }
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt");

    const gpgProcess = spawnGpgProcess(cmd, this.getSpawnOptions(), "message");
    return collectGpgMessage(gpgProcess, encryptedContent, signal);
  }

  /**
   * Decrypt a file and return the path to the decrypted file with original filename
   * Uses streaming approach to handle large files efficiently (similar to legacy client)
   * @param filepath - Path to the encrypted file
   * @returns Promise with path to decrypted file
   */
  async decryptFile(
    storage: Storage,
    itemDirectory: PathBuilder,
    filepath: string,
    signal?: AbortSignal,
  ): Promise<string> {
    throwIfAborted(signal);
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt", filepath);
    const tempDir = storage.createTempDir("securedrop-decrypt-");
    const tempGpgOutput = tempDir.join("decrypted.gz");

    try {
      const gpgProcess = spawnGpgProcess(cmd, this.getSpawnOptions(), "file");
      await writeGpgOutputToFile(gpgProcess, tempGpgOutput, signal);
      const finalOutputPath = await this.decompressGpgOutput(
        tempGpgOutput,
        itemDirectory,
        filepath,
        signal,
      );
      return finalOutputPath;
    } finally {
      await removeDirectoryIfExists(tempDir.path);
    }
  }

  private async decompressGpgOutput(
    gzipFilePath: string,
    itemDirectory: PathBuilder,
    encryptedFilePath: string,
    signal?: AbortSignal,
  ): Promise<string> {
    let finalOutputPath: string | null = null;
    try {
      throwIfAborted(signal);
      const originalFilename = await this.readGzipHeaderFilenameFromFile(
        gzipFilePath,
        signal,
      );
      const finalFilename =
        originalFilename || path.basename(encryptedFilePath, ".gpg");
      finalOutputPath = itemDirectory.join(finalFilename);
      await this.decompressGzipFileAtomically(
        gzipFilePath,
        itemDirectory,
        finalOutputPath,
        signal,
      );
      return finalOutputPath;
    } catch (error) {
      if (isCancellation(error)) {
        throw createAbortError();
      }
      if (error instanceof CryptoError) {
        throw error;
      }
      throw new CryptoError(
        "Failed to decompress decrypted file",
        asError(error),
      );
    }
  }

  /**
   * Encrypts a message to a source given the source public key. Message
   * will be encrypted to source and journalist public keys.
   * @param plaintext - The message plaintext
   * @param sourcePublicKey - Source PGP public key
   * @returns Promise<string> - The encrypted ciphertext
   */
  async encryptSourceMessage(
    plaintext: string,
    sourcePublicKey: string,
  ): Promise<string> {
    return encryptMessage(plaintext, [
      sourcePublicKey,
      await this.getSubmissionKey(),
    ]);
  }

  /**
   * Stream decompress a gzip file to another file (memory efficient)
   * Similar to legacy client's safe_copyfileobj approach
   */
  private async streamDecompressGzipFile(
    gzipFilePath: string,
    outputPath: string,
    signal?: AbortSignal,
  ): Promise<void> {
    const readStream = fs.createReadStream(gzipFilePath);
    const writeStream = fs.createWriteStream(outputPath, { flags: "wx" });
    const gunzip = createGunzip();

    await pipeline(
      readStream,
      gunzip,
      createDecryptedByteLimit("Decompressed file"),
      writeStream,
      { signal },
    );
  }

  private async decompressGzipFileAtomically(
    gzipFilePath: string,
    itemDirectory: PathBuilder,
    finalOutputPath: string,
    signal?: AbortSignal,
  ): Promise<void> {
    throwIfAborted(signal);
    const temporaryDirectory = fs.mkdtempSync(
      itemDirectory.join(".securedrop-decrypt-"),
    );
    const temporaryOutputPath = path.join(temporaryDirectory, "plaintext");

    try {
      await settleAbortable(
        this.streamDecompressGzipFile(
          gzipFilePath,
          temporaryOutputPath,
          signal,
        ),
        signal,
      );
      throwIfAborted(signal);
      await syncFile(temporaryOutputPath, signal);
      throwIfAborted(signal);
      await publishFileWithoutReplace(
        temporaryOutputPath,
        finalOutputPath,
        signal,
      );
    } finally {
      await removeDirectoryIfExists(temporaryDirectory);
    }
  }

  /**
   * Read gzip header filename from a file on disk (without loading entire file)
   */
  private async readGzipHeaderFilenameFromFile(
    filePath: string,
    signal?: AbortSignal,
  ): Promise<UnsafePathComponent | null> {
    throwIfAborted(signal);
    const file = await fs.promises.open(filePath, "r");
    try {
      throwIfAborted(signal);
      const header = Buffer.alloc(GZIP_HEADER_READ_BYTES);
      const { bytesRead } = await settleAbortable(
        file.read(header, 0, GZIP_HEADER_READ_BYTES, 0),
        signal,
      );
      return this.readGzipHeaderFilename(header.subarray(0, bytesRead));
    } finally {
      await file.close();
    }
  }

  /**
   * Extract original filename from gzip header
   */
  private readGzipHeaderFilename(data: Buffer): UnsafePathComponent | null {
    if (data.length < GZIP_FIXED_HEADER_BYTES) {
      throw new Error("Data too short to be a valid gzip file");
    }

    if (!data.subarray(0, 2).equals(GZIP_MAGIC)) {
      throw new Error(
        `Not a gzipped file (got ${data.subarray(0, 2).toString("hex")})`,
      );
    }

    if (data[2] !== 8) {
      throw new Error("Unknown compression method");
    }

    const flags = data[3];
    if ((flags & GZIP_FILENAME_FLAG) === 0) {
      return null;
    }
    return decodeGzipFilename(data, gzipFilenameOffset(data));
  }
}

/**
 * Encrypts a message to a source to the specified recipients
 * @param plaintext - The message plaintext
 * @param recipientPublicKeys - ASCII-encoded armored public keys for message recipients
 * @returns Promise<string> - The encrypted ciphertext
 */
export async function encryptMessage(
  plaintext: string,
  recipientPublicKeys: string[],
): Promise<string> {
  const publicKeys = await Promise.all(
    recipientPublicKeys.map((recipient) =>
      openpgp.readKey({ armoredKey: recipient }),
    ),
  );

  return await openpgp.encrypt({
    message: await openpgp.createMessage({ text: plaintext }),
    encryptionKeys: publicKeys,
  });
}
