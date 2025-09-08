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

/*
Create two separate methods:
 proxyJSON
 proxyStream
  - takes writer (not filepath)
  - takes in progress for incremental resume
*/

// // Proxies a network request through sd-proxy
// // For streaming requests, `downloadPath` must be specified as
// // the file location where stream data is downloaded
// export async function proxy(
//   request: ProxyRequest,
//   downloadPath?: string,
//   abortSignal?: AbortSignal,
// ): Promise<ProxyResponse> {
//   const proxyCommand = buildProxyCommand(abortSignal);

//   if (request.stream) {
//     if (!downloadPath) {
//       return Promise.reject(
//         `Error: no download path specified for streaming request`,
//       );
//     }
//     try {
//       return proxyStreamRequest(request, proxyCommand, downloadPath);
//     } catch (err) {
//       return Promise.reject(`Error proxying streaming request: ${err}`);
//     }
//   }
//   return proxyJSONRequest(request, proxyCommand);
// }

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
  proxyCommand?: ProxyCommand,
): Promise<ProxyJSONResponse> {
  const command = proxyCommand ? proxyCommand : buildProxyCommand(abortSignal);
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

    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}

// Streams proxy request through sd-proxy, writing stream output to
// the provided writeStream.
export async function proxyStreamRequest(
  request: ProxyRequest,
  writeStream: Writable,
  offset?: number,
  abortSignal?: AbortSignal,
  proxyCommand?: ProxyCommand,
): Promise<ProxyResponse> {
  const command = proxyCommand ? proxyCommand : buildProxyCommand(abortSignal);
  return new Promise((resolve, reject) => {
    let bytesWritten = 0;
    let stdout = "";
    let stderr = "";
    const process = child_process.spawn(command.command, command.options, {
      env: Object.fromEntries(command.env),
      timeout: command.timeout,
      signal: command.abortSignal,
    });

    process.stdout.pipe(writeStream);

    process.stdout.on("data", (data) => {
      bytesWritten += data.length;
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
    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}

function buildProxyCommand(abortSignal?: AbortSignal): ProxyCommand {
  let command = "";
  let commandOptions: string[] = [];
  const env: Map<string, string> = new Map();

  if (import.meta.env.MODE == "development") {
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
