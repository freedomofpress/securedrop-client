import child_process from "node:child_process";

export type ProxyRequest = {
  method: string;
  path_query: string;
  stream: false;
  body: string;
  headers: object;
};

export type ProxyResponse = {
  stdout: string;
  stderr: string;
  code: number;
};

const DEFAULT_PROXY_VM_NAME = "sd-proxy";

export async function proxy(request: ProxyRequest): Promise<ProxyResponse> {
  let proxyCommand = "";
  if (import.meta.env.MODE != "development") {
    const proxyVmName = import.meta.env.VITE_PROXY_VM_NAME
      ? import.meta.env.VITE_PROXY_VM_NAME
      : DEFAULT_PROXY_VM_NAME;
    proxyCommand = `/usr/lib/qubes/qrexec-client-vm ${proxyVmName} securedrop.Proxy`;
  } else {
    proxyCommand = import.meta.env.VITE_SD_PROXY_CMD;
  }
  return proxyInner(
    request,
    proxyCommand,
    import.meta.env.VITE_SD_PROXY_ORIGIN,
  );
}

export async function proxyInner(
  request: ProxyRequest,
  proxyCommand: string,
  proxyOrigin: string,
): Promise<ProxyResponse> {
  return new Promise((resolve, reject) => {
    const process = child_process.spawn(proxyCommand, [], {
      env: { SD_PROXY_ORIGIN: proxyOrigin },
    });

    let stdout = "";
    let stderr = "";
    process.stdout.on("data", (data) => {
      stdout += data.toString();
    });

    process.stderr.on("data", (data) => {
      stderr += data.toString();
    });

    process.on("close", (code) => {
      if (code === 0) {
        resolve({ stdout, stderr, code } as ProxyResponse);
      } else {
        reject(new Error(`Process exited with code ${code}: ${stderr}`));
      }
    });

    process.on("error", (error) => {
      reject(error);
    });

    process.stdin.write(JSON.stringify(request) + "\n");
    process.stdin.end();
  });
}
