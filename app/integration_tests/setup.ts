import { execSync } from "child_process";
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
  const stdout = execSync(
    "cargo metadata --format-version 1 | jq -r '.target_directory'",
  )
    .toString()
    .trim();
  globalThis.sdProxyCommand = `${stdout}/debug/securedrop-proxy`;
  globalThis.sdProxyOrigin = "http://localhost:8081";

  // pull + start httpbin on 8081
  execSync(`podman pull ${HTTPBIN_IMAGE}`);
  execSync(`podman run -d -p 8081:80 ${HTTPBIN_IMAGE}`);
});

afterAll(() => {
  const containerID = execSync(
    `podman ps --filter 'ancestor=${HTTPBIN_IMAGE}' --format '{{.ID}}'`,
  )
    .toString()
    .trim();
  execSync(`podman stop ${containerID}`);

  delete globalThis.sdProxyCommand;
  delete globalThis.sdProxyOrigin;
});
