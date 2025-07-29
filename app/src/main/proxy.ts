import child_process from "node:child_process";
import fs from "fs";
import path from "path";
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
const DEFAULT_STREAM_MAX_RETRY_ATTEMPTS = 3;

// Proxies a network request through sd-proxy
// For streaming requests, `downloadPath` must be specified as
// the file location where stream data is downloaded
export async function proxy(
  request: ProxyRequest,
  downloadPath?: string,
  abortSignal?: AbortSignal,
): Promise<ProxyResponse> {
  let command = "";
  let commandOptions: string[] = [];

  if (import.meta.env.MODE == "development") {
    command = __PROXY_CMD__;
  } else {
    command = "/usr/lib/qubes/qrexec-client-vm";

    const proxyVmName = DEFAULT_PROXY_VM_NAME;
    commandOptions = [proxyVmName, "securedrop.Proxy"];
  }
  const proxyCommand: ProxyCommand = {
    command: command,
    options: commandOptions,
    proxyOrigin: __PROXY_ORIGIN__,
    timeout: DEFAULT_PROXY_CMD_TIMEOUT_MS,
    abortSignal: abortSignal,
  };

  if (request.stream) {
    if (!downloadPath) {
      return Promise.reject(
        `Error: no download path specified for streaming request`,
      );
    }
    try {
      return proxyStreamRequest(
        request,
        proxyCommand,
        downloadPath,
        DEFAULT_STREAM_MAX_RETRY_ATTEMPTS,
      );
    } catch (err) {
      return Promise.reject(`Error proxying streaming request: ${err}`);
    }
  }
  return proxyJSONRequest(request, proxyCommand);
}

function parseJSONResponse(response: string): ProxyJSONResponse {
  const result = JSON.parse(response);
  const status = result["status"];
  let body = result["body"];
  try {
    body = JSON.parse(result["body"]);
  } catch {
    // do nothing
  }

  if (!status) {
    throw new Error(`Invalid response: no status code found.\n`);
  }
  const error =
    (status >= 400 && status < 500 && status != 404) ||
    (status >= 500 && status < 600);

  return {
    error,
    data: body,
    status: status,
    headers: result["headers"] || {},
  };
}

export async function proxyJSONRequest(
  request: ProxyRequest,
  command: ProxyCommand,
): Promise<ProxyJSONResponse> {
  return new Promise((resolve, reject) => {
    const process = child_process.spawn(command.command, command.options, {
      env: { SD_PROXY_ORIGIN: command.proxyOrigin },
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

    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}

export async function proxyStreamRequest(
  request: ProxyRequest,
  command: ProxyCommand,
  downloadPath: string,
  maxRetryAttempts: number,
): Promise<ProxyResponse> {
  let writeStream: fs.WriteStream;
  try {
    const downloadDir = path.dirname(downloadPath);
    await fs.promises.mkdir(downloadDir, { recursive: true });
    writeStream = fs.createWriteStream(downloadPath);
  } catch (err) {
    return Promise.reject(
      `Error opening write stream to download path: ${err}`,
    );
  }
  let retries = 0;
  let lastErr;
  while (retries < maxRetryAttempts) {
    try {
      return proxyStreamInner(
        request,
        command,
        writeStream,
        writeStream.bytesWritten,
      );
    } catch (err) {
      lastErr = err;
      retries += 1;
      console.log(
        `Error streaming proxy request: ${err}.\nRetrying... attempts=${retries}, remaining=${maxRetryAttempts - retries}`,
      );
    }
  }
  return Promise.reject(
    `Failed to proxy stream request, max retry attempts exceeded. Error ${lastErr}`,
  );
}

// Streams proxy request through sd-proxy, writing stream output to
// the provided writeStream.
export async function proxyStreamInner(
  request: ProxyRequest,
  command: ProxyCommand,
  writeStream: Writable,
  offset?: number,
): Promise<ProxyResponse> {
  return new Promise((resolve, reject) => {
    let stderr = "";
    let stdout = "";
    const process = child_process.spawn(command.command, command.options, {
      env: { SD_PROXY_ORIGIN: command.proxyOrigin },
      timeout: command.timeout,
      signal: command.abortSignal,
    });

    process.stdout.pipe(writeStream);

    process.stdout.on("data", (data) => {
      stdout += data;
    });

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
        reject(`Process terminated with signal ${signal}`);
      }
      if (code != 0) {
        reject(`Process exited with non-zero code ${code}: ${stderr}`);
      }
      try {
        // If we receive JSON data, parse and return
        resolve(parseJSONResponse(stdout));
      } catch {
        try {
          const header = JSON.parse(stderr);
          resolve({ sha256sum: header["headers"]["etag"] || "" });
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
    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}
