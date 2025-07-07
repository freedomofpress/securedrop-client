import child_process from "node:child_process";
import fs from "fs";
import path from "path";

import { JSONObject } from "./utils";
import { Writable } from "node:stream";

export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream: boolean;
  body?: string;
  headers: object;
};

export type ProxyResponse = ProxyJSONResponse | ProxyStreamResponse;

export type ProxyJSONResponse = {
  data: JSONObject;
  status: number;
  headers: Map<string, string>;
};

export type ProxyStreamResponse = {
  sha256sum: string;
};

const DEFAULT_PROXY_VM_NAME = "sd-proxy";
const DEFAULT_PROXY_CMD_TIMEOUT_MS = 5000;

// Proxies a network request through sd-proxy
// For streaming requests, `downloadPath` must be specified as
// the file location where stream data is downloaded
export async function proxy(
  request: ProxyRequest,
  downloadPath?: string,
): Promise<ProxyResponse> {
  let proxyCommand = "";
  let proxyCommandOptions: string[] = [];

  if (import.meta.env.MODE == "development") {
    proxyCommand = import.meta.env.VITE_SD_PROXY_CMD;
  } else {
    proxyCommand = "/usr/lib/qubes/qrexec-client-vm";

    const proxyVmName =
      import.meta.env.VITE_PROXY_VM_NAME || DEFAULT_PROXY_VM_NAME;
    proxyCommandOptions = [proxyVmName, "securedrop.Proxy"];
  }

  if (request.stream) {
    if (!downloadPath) {
      return Promise.reject(
        `Error: no download path specified for streaming request`,
      );
    }
    try {
      const downloadDir = path.dirname(downloadPath);
      await fs.promises.mkdir(downloadDir, { recursive: true });
      const writeStream = fs.createWriteStream(downloadPath);
      return proxyStreamingInner(
        request,
        proxyCommand,
        proxyCommandOptions,
        import.meta.env.VITE_SD_PROXY_ORIGIN,
        DEFAULT_PROXY_CMD_TIMEOUT_MS,
        writeStream,
      );
    } catch (err) {
      return Promise.reject(`Error proxying streaming request: ${err}`);
    }
  }
  return proxyRequestInner(
    request,
    proxyCommand,
    proxyCommandOptions,
    import.meta.env.VITE_SD_PROXY_ORIGIN,
    DEFAULT_PROXY_CMD_TIMEOUT_MS,
  );
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

export async function proxyRequestInner(
  request: ProxyRequest,
  proxyCommand: string,
  proxyCommandOptions: string[],
  proxyOrigin: string,
  proxyCommandTimeout: number,
): Promise<ProxyJSONResponse> {
  return new Promise((resolve, reject) => {
    const process = child_process.spawn(proxyCommand, proxyCommandOptions, {
      env: { SD_PROXY_ORIGIN: proxyOrigin },
      timeout: proxyCommandTimeout,
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

// Streams proxy request through sd-proxy, writing stream output to
// the provided writeStream.
export async function proxyStreamingInner(
  request: ProxyRequest,
  proxyCommand: string,
  proxyCommandOptions: string[],
  proxyOrigin: string,
  proxyCommandTimeout: number,
  writeStream: Writable,
): Promise<ProxyStreamResponse> {
  return new Promise((resolve, reject) => {
    let stderr = "";
    const process = child_process.spawn(proxyCommand, proxyCommandOptions, {
      env: { SD_PROXY_ORIGIN: proxyOrigin },
      timeout: proxyCommandTimeout,
    });

    process.stdout.pipe(writeStream);

    process.stderr.on("data", (data) => {
      stderr += data;
    });

    writeStream.on("error", (err) => {
      throw new Error(`Error writing stream data: ${err}`);
    });

    process.on("close", async (code, signal) => {
      writeStream.end();
      if (signal) {
        reject(`Process terminated with signal ${signal}`);
      }
      if (code != 0) {
        reject(`Process exited with non-zero code ${code}: ${stderr}`);
      }
      // Read headers from stderr
      try {
        const header = JSON.parse(stderr);
        resolve({
          sha256sum: header["headers"]["etag"] || "",
        });
      } catch (err) {
        reject(`Error reading headers from proxy stderr: ${err}`);
      }
    });

    process.on("error", (err) => {
      reject(`Proxy process error: ${err}`);
    });

    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}
