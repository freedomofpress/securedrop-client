import { execSync } from "child_process";
import { beforeAll, afterAll } from "vitest";
import { GenericContainer, StartedTestContainer } from "testcontainers";

const HTTPBIN_IMAGE = "kennethreitz/httpbin";

declare global {
  var sdProxyCommand: string;
  var sdProxyOrigin: string;
  var httpbinContainer: StartedTestContainer;
}

export {};

beforeAll(async () => {
  // Build sd-proxy binary
  execSync("make -C ../proxy build");
  const stdout = execSync("cargo metadata --format-version 1")
    .toString()
    .trim();
  const targetDir = JSON.parse(stdout)["target_directory"];
  globalThis.sdProxyCommand = `${targetDir}/debug/securedrop-proxy`;
  globalThis.sdProxyOrigin =
    import.meta.env.VITE_HTTPBIN_URL || "http://localhost:8081";

  // Running in localdev, start httpbin container
  if (import.meta.env.NODE_ENV != "ci") {
    globalThis.httpbinContainer = await new GenericContainer(HTTPBIN_IMAGE)
      .withExposedPorts(80)
      .start();

    globalThis.sdProxyOrigin = `http://${httpbinContainer.getHost()}:${httpbinContainer.getMappedPort(80)}`;
  }
}, 60000);

afterAll(async () => {
  if (import.meta.env.NODE_ENV != "ci") {
    await globalThis.httpbinContainer.stop();
  }
});
