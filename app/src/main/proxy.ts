import child_process from "node:child_process";
import { Writable } from "node:stream";

import type {
  ProxyRequest,
  ProxyResponse,
  ProxyCommand,
  ProxyJSONResponse,
  ms,
} from "../types";

const DEFAULT_PROXY_VM_NAME = "sd-proxy";
const DEFAULT_PROXY_CMD_TIMEOUT_MS = 5000 as ms;

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

export async function proxyJSONRequest(
  request: ProxyRequest,
  abortSignal?: AbortSignal,
): Promise<ProxyJSONResponse> {
  return proxyJSONRequestInner(request, buildProxyCommand(abortSignal));
}

export async function proxyJSONRequestInner(
  request: ProxyRequest,
  command: ProxyCommand,
): Promise<ProxyJSONResponse> {
  return new Promise((resolve, reject) => {
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

    request.stream = request.stream ?? false;
    process.stdin.write(JSON.stringify(request) + "\n");
  });
}

// Streams proxy request through sd-proxy, writing stream output to
// the provided writeStream.
export async function proxyStreamRequest(
  request: ProxyRequest,
  writeStream: Writable,
  offset?: number,
  abortSignal?: AbortSignal,
): Promise<ProxyResponse> {
  return proxyStreamRequestInner(
    request,
    buildProxyCommand(abortSignal),
    writeStream,
    offset,
  );
}

export async function proxyStreamRequestInner(
  request: ProxyRequest,
  command: ProxyCommand,
  writeStream: Writable,
  offset?: number,
): Promise<ProxyResponse> {
  return new Promise((resolve, reject) => {
    const process = child_process.spawn(command.command, command.options, {
      env: Object.fromEntries(command.env),
      timeout: command.timeout,
      signal: command.abortSignal,
    });

    // Attach provided `writeStream` to the standard output of the proxy command. This will write
    // contents directly to the `writeStream`.
    process.stdout.pipe(writeStream);

    // Store stdout as buffer array to avoid binary data corruption, and track bytes written
    // to allow resuming incremental progress.
    const stdoutChunks: Buffer[] = [];
    let bytesWritten = 0;
    process.stdout.on("data", (data) => {
      bytesWritten += data.length;
      stdoutChunks.push(data);
    });

    let stderr = "";
    process.stderr.on("data", (data) => {
      stderr += data;
    });

    process.stdout.on("error", (err) => {
      reject(`Error reading stream data: ${err}`);
    });

    writeStream.on("error", (err) => {
      reject(`Error writing stream data: ${err}`);
    });

    process.on("close", async (code, signal) => {
      writeStream.end();

      if (signal) {
        resolve({
          complete: false,
          error: new Error(`Process terminated with signal ${signal}`),
          bytesWritten: bytesWritten,
        });
      }
      if (code != 0) {
        resolve({
          complete: false,
          error: new Error(
            `Process exited with non-zero code ${code}: ${stderr}`,
          ),
          bytesWritten: bytesWritten,
        });
      }
      try {
        // If we receive JSON data, parse and return
        // Convert buffer chunks to string only when needed for JSON parsing
        const stdout = Buffer.concat(stdoutChunks).toString("utf8");
        resolve(parseJSONResponse(stdout));
      } catch {
        try {
          const header = JSON.parse(stderr);
          resolve({
            complete: true,
            sha256sum: header["headers"]["etag"] || "",
            bytesWritten: bytesWritten,
          });
        } catch (err) {
          reject(`Error reading headers from proxy stderr: ${err}`);
        }
      }
    });

    process.on("error", (err) => {
      reject(`Proxy process error: ${err}`);
    });

    if (offset && offset != 0) {
      request.headers["Range"] = `bytes=${offset}-`;
    }
    request.stream = true;
    process.stdin.write(JSON.stringify(request) + "\n");
  });
}

function buildProxyCommand(abortSignal?: AbortSignal): ProxyCommand {
  let command = "";
  let commandOptions: string[] = [];
  const env: Map<string, string> = new Map();

  if (import.meta.env.MODE == "development" || import.meta.env.MODE == "test") {
    command = __PROXY_CMD__;
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
    timeout: DEFAULT_PROXY_CMD_TIMEOUT_MS,
    abortSignal: abortSignal,
  };
}
