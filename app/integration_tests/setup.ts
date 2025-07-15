import { exec, execSync } from "child_process";
import { beforeAll, afterAll } from "vitest";

const HTTPBIN_IMAGE = "docker.io/kennethreitz/httpbin";

declare global {
  var sdProxyCommand: string;
  var sdProxyOrigin: string;
}

export {};

beforeAll(() => {
  // Build sd-proxy binary
  execSync("make -C ../proxy build");
  const stdout = execSync("cargo metadata --format-version 1")
    .toString()
    .trim();
  const targetDir = JSON.parse(stdout)["target_directory"];
  globalThis.sdProxyCommand = `${targetDir}/debug/securedrop-proxy`;
  globalThis.sdProxyOrigin =
    import.meta.env.VITE_HTTPBIN_URL || "http://localhost:8081";

  // Pull + start httpbin on 8081 in localdev
  // TODO(vicki): use testcontainers instead?
  if (import.meta.env.NODE_ENV != "ci") {
    execSync(`podman pull ${HTTPBIN_IMAGE}`);
    execSync(`podman run -d -p 8081:80 ${HTTPBIN_IMAGE}`);
  }
}, 60000);

afterAll(() => {
  delete globalThis.sdProxyCommand;
  delete globalThis.sdProxyOrigin;

  if (import.meta.env.NODE_ENV != "ci") {
    const containerID = execSync(
      `podman ps --filter 'ancestor=${HTTPBIN_IMAGE}' --format '{{.ID}}'`,
      { timeout: 5000 },
    )
      .toString()
      .trim();
    exec(`podman stop ${containerID}`);
  }
});
