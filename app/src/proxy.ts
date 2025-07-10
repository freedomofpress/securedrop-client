import child_process from "node:child_process";
import fs from "fs";
import path from "path";
import { readFile } from "fs/promises";

import { JSONObject } from "./utils";
import { Writable } from "node:stream";

export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream: boolean;
  body?: string;
  headers: Map<string, string>;
};

export type ProxyCommand = {
  command: string;
  options: string[];
  proxyOrigin: string;
  timeoutMs: number;
};

export type ProxyResponse = ProxyJSONResponse | ProxyStreamResponse;

export type ProxyJSONResponse = {
  data: JSONObject;
  status: number;
  headers: Map<string, string>;
};

export type ProxyStreamResponse = {
  sha256sum: string;
  status: number;
};

const DEFAULT_PROXY_VM_NAME = "sd-proxy";
const DEFAULT_PROXY_CMD_TIMEOUT_MS = 5000;
const DEFAULT_STREAM_MAX_RETRY_ATTEMPTS = 3;

// Proxies a network request through sd-proxy
// For streaming requests, `downloadPath` must be specified as
// the file location where stream data is downloaded
export async function proxy(
  request: ProxyRequest,
  downloadPath?: string,
): Promise<ProxyResponse> {
  let command = "";
  let commandOptions: string[] = [];

  if (import.meta.env.MODE == "development") {
    command = import.meta.env.VITE_SD_PROXY_CMD;
  } else {
    command = "/usr/lib/qubes/qrexec-client-vm";

    const proxyVmName =
      import.meta.env.VITE_PROXY_VM_NAME || DEFAULT_PROXY_VM_NAME;
    commandOptions = [proxyVmName, "securedrop.Proxy"];
  }
  const proxyCommand = {
    command: command,
    options: commandOptions,
    proxyOrigin: import.meta.env.VITE_SD_PROXY_ORIGIN,
    timeoutMs: DEFAULT_PROXY_CMD_TIMEOUT_MS,
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
  const body = result["body"];

  if (!status) {
    throw new Error(`Invalid response: no status code found.\n`);
  }
  // Ignore 404s for 4xx error response
  if (status >= 400 && status < 500 && status != 404) {
    throw new Error(`Client error ${status}: ${body}`);
  } else if (status >= 500 && status < 600) {
    throw new Error(`Server error ${status}: ${body}`);
  }

  return {
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
      timeout: command.timeoutMs,
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

async function proxyStreamRequest(
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
      const response = await proxyStreamInner(
        request,
        command,
        writeStream,
        writeStream.bytesWritten,
      );
      // On HTTP error response, return JSON response
      if (response.status >= 400) {
        const responseData = await readFile(downloadPath, "utf8");
        return Promise.resolve(parseJSONResponse(responseData));
      }
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
  offset: number,
): Promise<ProxyStreamResponse> {
  return new Promise((resolve, reject) => {
    let stderr = "";
    const process = child_process.spawn(command.command, command.options, {
      env: { SD_PROXY_ORIGIN: command.proxyOrigin },
      timeout: command.timeoutMs,
    });

    process.stdout.pipe(writeStream);

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
      // sd-proxy writes response headers to stderr
      try {
        const header = JSON.parse(stderr);
        resolve({
          status: header["headers"]["status"] || 0,
          sha256sum: header["headers"]["etag"] || "",
        });
      } catch (err) {
        reject(`Error reading headers from proxy stderr: ${err}`);
      }
    });

    process.on("error", (err) => {
      reject(`Proxy process error: ${err}`);
    });

    if (offset && offset != 0) {
      request.headers.set("Range", `bytes=${offset}-`);
    }
    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}
