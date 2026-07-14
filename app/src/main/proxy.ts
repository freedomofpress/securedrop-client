import child_process from "node:child_process";
import { channel } from "node:diagnostics_channel";
import path from "node:path";
import { Writable } from "node:stream";
import { finished } from "node:stream/promises";

import type {
  ProxyRequest,
  ProxyResponse,
  ProxyCommand,
  ProxyJSONResponse,
  ms,
  sec,
} from "../types";

const DEFAULT_PROXY_VM_NAME = "sd-proxy";

// To avoid timeout confusion, timeouts SHOULD be either the same as or longer
// than the proxy's request-level timeout.
export const DEFAULT_PROXY_CMD_TIMEOUT_MS = 10_000 as ms;
export const MESSAGE_REPLY_DOWNLOAD_TIMEOUT_MS = 20_000 as ms;
export const LEGACY_STREAM_JSON_MAX_BYTES = 1024 * 1024;
export const STREAM_METADATA_MAX_BYTES = 1024 * 1024;
export const STREAM_CAPTURE_DIAGNOSTICS_CHANNEL =
  "securedrop.proxy.stream-capture";

export type StreamCaptureDiagnostics = {
  stdoutBytesObserved: number;
  legacyBytesCaptured: number;
  metadataBytesObserved: number;
  metadataBytesCaptured: number;
};

const streamCaptureDiagnostics = channel(STREAM_CAPTURE_DIAGNOSTICS_CHANNEL);

class BoundedCapture {
  private readonly buffer: Buffer;
  private bytesCaptured = 0;
  private totalBytes = 0;

  constructor(maxBytes: number) {
    this.buffer = Buffer.alloc(maxBytes);
  }

  append(chunk: Buffer): void {
    this.totalBytes += chunk.length;
    const bytesToCopy = Math.min(
      chunk.length,
      this.buffer.length - this.bytesCaptured,
    );
    if (bytesToCopy > 0) {
      chunk.copy(this.buffer, this.bytesCaptured, 0, bytesToCopy);
      this.bytesCaptured += bytesToCopy;
    }
  }

  get overflowed(): boolean {
    return this.totalBytes > this.buffer.length;
  }

  get capturedBytes(): number {
    return this.bytesCaptured;
  }

  get observedBytes(): number {
    return this.totalBytes;
  }

  toString(): string {
    return this.buffer.subarray(0, this.bytesCaptured).toString();
  }
}

function parseJSONResponse(response: string): ProxyJSONResponse {
  const result = JSON.parse(response);
  const status = result["status"];
  let body = result["body"];
  if (!status) {
    throw new Error(`Invalid response: no status code found.\n`);
  }
  const error =
    (status >= 400 && status < 500) || (status >= 500 && status < 600);

  if (!error) {
    try {
      if (body && typeof body === "string") {
        body = JSON.parse(body);
      }
    } catch (e) {
      console.log(
        `Failed to parse response body as JSON: ${result["status"]}: ${result["body"]}: ${e}`,
      );
    }
  }
  return {
    error,
    data: body,
    status: status,
    headers: result["headers"]
      ? new Map(Object.entries(result["headers"]))
      : new Map(),
  };
}

function parseStreamMetadata(
  response: string,
  bytesWritten: number,
): ProxyResponse {
  const result = JSON.parse(response);
  const rawHeaders = result["headers"];
  if (
    !rawHeaders ||
    typeof rawHeaders !== "object" ||
    Array.isArray(rawHeaders) ||
    Object.values(rawHeaders).some((value) => typeof value !== "string")
  ) {
    throw new Error("Invalid stream metadata: headers must be an object");
  }

  const status = result["status"];
  if (
    status !== undefined &&
    (!Number.isInteger(status) || status < 100 || status > 599)
  ) {
    throw new Error("Invalid stream metadata: invalid status code");
  }

  const headers = new Map<string, string>(Object.entries(rawHeaders));
  const error =
    typeof status === "number" &&
    ((status >= 400 && status < 500) || (status >= 500 && status < 600));
  if (error) {
    return { error, data: null, status, headers };
  }

  return {
    complete: true,
    sha256sum: headers.get("etag") || "",
    bytesWritten,
  };
}

function parseLegacyStreamError(response: string): ProxyJSONResponse {
  const result = parseJSONResponse(response);
  if (!result.error) {
    throw new Error("Legacy stream response did not contain an HTTP error");
  }
  return result;
}

type StreamCloseContext = {
  code: number | null;
  signal: NodeJS.Signals | null;
  writeStream: Writable;
  bytesWritten: number;
  stderr: BoundedCapture;
  legacyJSON: BoundedCapture;
};

async function finishStreamResponse(
  context: StreamCloseContext,
): Promise<ProxyResponse> {
  context.writeStream.end();
  try {
    await finished(context.writeStream, { readable: false });
  } catch (err) {
    return Promise.reject(`Error flushing write stream: ${err}`);
  }

  if (context.signal) {
    return {
      complete: false,
      error: new Error(`Process terminated with signal ${context.signal}`),
      bytesWritten: context.bytesWritten,
    };
  }
  if (context.code != 0) {
    return {
      complete: false,
      error: new Error(
        `Process exited with non-zero code ${context.code}: ${context.stderr.toString()}`,
      ),
      bytesWritten: context.bytesWritten,
    };
  }
  if (context.stderr.overflowed) {
    return Promise.reject(
      `Proxy stderr exceeded ${STREAM_METADATA_MAX_BYTES} bytes`,
    );
  }
  if (context.stderr.toString().trim()) {
    try {
      return parseStreamMetadata(
        context.stderr.toString(),
        context.bytesWritten,
      );
    } catch (err) {
      return Promise.reject(`Error reading metadata from proxy stderr: ${err}`);
    }
  }
  if (context.legacyJSON.overflowed) {
    return Promise.reject(
      `Legacy proxy JSON response exceeded ${LEGACY_STREAM_JSON_MAX_BYTES} bytes`,
    );
  }

  try {
    return parseLegacyStreamError(context.legacyJSON.toString());
  } catch (err) {
    return Promise.reject(`Error reading legacy proxy JSON response: ${err}`);
  }
}

export async function proxyJSONRequest(
  request: ProxyRequest,
  abortSignal?: AbortSignal,
  timeout?: ms,
): Promise<ProxyJSONResponse> {
  return proxyJSONRequestInner(
    request,
    buildProxyCommand(abortSignal, timeout),
  );
}

export async function proxyJSONRequestInner(
  request: ProxyRequest,
  command: ProxyCommand,
): Promise<ProxyJSONResponse> {
  return new Promise((resolve, reject) => {
    // The path in `command.command` is hardcoded and not user input
    // nosemgrep: javascript.lang.security.detect-child-process.detect-child-process
    const process = child_process.spawn(command.command, command.options, {
      env: Object.fromEntries(command.env),
      timeout: command.timeout,
      signal: command.abortSignal,
    });

    let stdout = "";
    let stderr = "";
    process.stdout.on("data", (data) => {
      stdout += data.toString();
    });

    process.stderr.on("data", (data) => {
      stderr += data.toString();
    });

    process.on("close", (code, signal) => {
      if (signal) {
        reject(new Error(`Process terminated with signal ${signal}`));
      } else if (code != 0) {
        reject(
          new Error(`Process exited with non-zero code ${code}: ${stderr}`),
        );
      } else {
        try {
          resolve(parseJSONResponse(stdout));
        } catch (err) {
          reject(err);
        }
      }
    });

    process.on("error", (error) => {
      reject(error);
    });

    process.stdin.on("error", (error) => {
      reject(error);
    });

    request.stream = request.stream ?? false;

    // Use the longer of the command- or request-level timeout, in seconds.
    const timeoutInSeconds = Math.floor(command.timeout / 1000);
    const defaultInSeconds = Math.floor(DEFAULT_PROXY_CMD_TIMEOUT_MS / 1000);
    request.timeout = Math.max(timeoutInSeconds, defaultInSeconds) as sec;

    try {
      process.stdin.write(JSON.stringify(request) + "\n");
    } catch (error) {
      reject(error);
    }
  });
}

// Callback type for reporting download progress
export type ProgressCallback = (bytesWritten: number) => void;

// Streams proxy request through sd-proxy, writing stream output to
// the provided writeStream.
export async function proxyStreamRequest(
  request: ProxyRequest,
  writeStream: Writable,
  offset?: number,
  abortSignal?: AbortSignal,
  timeout?: ms,
  onProgress?: ProgressCallback,
): Promise<ProxyResponse> {
  return proxyStreamRequestInner(
    request,
    buildProxyCommand(abortSignal, timeout),
    writeStream,
    offset,
    onProgress,
  );
}

export async function proxyStreamRequestInner(
  request: ProxyRequest,
  command: ProxyCommand,
  writeStream: Writable,
  offset?: number,
  onProgress?: ProgressCallback,
): Promise<ProxyResponse> {
  return new Promise((resolve, reject) => {
    // The path in `command.command` is hardcoded and not user input
    // nosemgrep: javascript.lang.security.detect-child-process.detect-child-process
    const process = child_process.spawn(command.command, command.options, {
      env: Object.fromEntries(command.env),
      timeout: command.timeout,
      signal: command.abortSignal,
    });

    // Attach the provided write stream directly to proxy stdout.
    process.stdout.pipe(writeStream);

    // Legacy proxies emit HTTP error envelopes on stdout. Retain only a fixed-size prefix.
    const legacyJSON = new BoundedCapture(LEGACY_STREAM_JSON_MAX_BYTES);
    let bytesWritten = 0;
    process.stdout.on("data", (data: Buffer) => {
      bytesWritten += data.length;
      legacyJSON.append(data);
      // Report progress to caller if callback is provided
      if (onProgress) {
        try {
          onProgress(bytesWritten);
        } catch (error) {
          reject(error);
        }
      }
    });

    const stderr = new BoundedCapture(STREAM_METADATA_MAX_BYTES);
    process.stderr.on("data", (data: Buffer) => {
      stderr.append(data);
    });

    process.stdout.on("error", (err) => {
      reject(`Error reading stream data: ${err}`);
    });

    writeStream.on("error", (err) => {
      reject(`Error writing stream data: ${err}`);
    });

    process.on("close", (code, signal) => {
      if (streamCaptureDiagnostics.hasSubscribers) {
        streamCaptureDiagnostics.publish({
          stdoutBytesObserved: bytesWritten,
          legacyBytesCaptured: legacyJSON.capturedBytes,
          metadataBytesObserved: stderr.observedBytes,
          metadataBytesCaptured: stderr.capturedBytes,
        } satisfies StreamCaptureDiagnostics);
      }
      void finishStreamResponse({
        code,
        signal,
        writeStream,
        bytesWritten,
        stderr,
        legacyJSON,
      }).then(resolve, reject);
    });

    process.on("error", (err) => {
      reject(`Proxy process error: ${err}`);
    });

    process.stdin.on("error", (error) => {
      reject(error);
    });

    if (offset && offset != 0) {
      request.headers["Range"] = `bytes=${offset}-`;
    }
    request.stream = true;

    // Use the longer of the command- or request-level timeout, in seconds.
    const timeoutInSeconds = Math.floor(command.timeout / 1000);
    const defaultInSeconds = Math.floor(DEFAULT_PROXY_CMD_TIMEOUT_MS / 1000);
    request.timeout = Math.max(timeoutInSeconds, defaultInSeconds) as sec;

    try {
      process.stdin.write(JSON.stringify(request) + "\n");
    } catch (error) {
      reject(error);
    }
  });
}

function buildProxyCommand(
  abortSignal?: AbortSignal,
  timeout?: ms,
): ProxyCommand {
  let command = "";
  let commandOptions: string[] = [];
  const env: Map<string, string> = new Map();

  if (
    import.meta.env.MODE == "development" ||
    import.meta.env.MODE == "test" ||
    import.meta.env.MODE == "mac-demo"
  ) {
    command = __PROXY_CMD__;
    if (import.meta.env.MODE == "mac-demo") {
      command = path.join(process.resourcesPath, "bin", "securedrop-proxy");
    }
    env.set("SD_PROXY_ORIGIN", __PROXY_ORIGIN__);
    env.set("DISABLE_TOR", "yes");
  } else {
    command = "/usr/lib/qubes/qrexec-client-vm";

    const proxyVmName = DEFAULT_PROXY_VM_NAME;
    commandOptions = [proxyVmName, "securedrop.Proxy"];
  }
  return {
    command: command,
    options: commandOptions,
    env: env,
    timeout: timeout || DEFAULT_PROXY_CMD_TIMEOUT_MS,
    abortSignal: abortSignal,
  };
}
