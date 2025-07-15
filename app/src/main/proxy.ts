import child_process from "node:child_process";
import type { ProxyRequest, ProxyResponse } from "../types";

const DEFAULT_PROXY_VM_NAME = "sd-proxy";
const DEFAULT_PROXY_CMD_TIMEOUT_MS = 5000;

export async function proxy(request: ProxyRequest): Promise<ProxyResponse> {
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

  return proxyInner(
    request,
    proxyCommand,
    proxyCommandOptions,
    import.meta.env.VITE_SD_PROXY_ORIGIN,
    DEFAULT_PROXY_CMD_TIMEOUT_MS,
  );
}

export async function proxyInner(
  request: ProxyRequest,
  proxyCommand: string,
  proxyCommandOptions: string[],
  proxyOrigin: string,
  proxyCommandTimeout: number,
): Promise<ProxyResponse> {
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
          const result = JSON.parse(stdout);
          const status = result["status"];
          const body = result["body"];

          if (!status) {
            reject(new Error(`Invalid response: no status code found.\n`));
          }
          // Ignore 404s for 4xx error response
          if (status >= 400 && status < 500 && status != 404) {
            reject(new Error(`Client error ${status}: ${body}`));
          } else if (status >= 500 && status < 600) {
            reject(new Error(`Server error ${status}: ${body}`));
          }

          resolve({
            data: JSON.parse(body),
            status: status,
            headers: result["headers"] || {},
          });
        } catch (error) {
          reject(error);
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
