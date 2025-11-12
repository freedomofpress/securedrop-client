import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import { resolve } from "path";
import { execSync } from "child_process";

// Check if we're running server tests by looking at command line args
const isRunningServerTests =
  process.argv.includes("--project=server") ||
  process.argv.some((arg) => arg.includes("server_tests"));

function buildProxyForServerTests() {
  if (!isRunningServerTests) {
    // Return empty strings for non-server tests (won't be used anyway)
    return "";
  }

  console.log("Building proxy for server tests...");

  // Build the proxy binary
  execSync("make -C ../proxy build", { stdio: "inherit" });

  // Get the path to the built binary
  const stdout = execSync("cargo metadata --format-version 1", {
    encoding: "utf-8",
  });
  const metadata = JSON.parse(stdout);
  const targetDir = metadata.target_directory;
  const proxyPath = `${targetDir}/debug/securedrop-proxy`;
  return resolve(proxyPath);
}

const sdProxyCmd = buildProxyForServerTests();

export default defineConfig({
  plugins: [react()],
  test: {
    setupFiles: [
      "./src/test-setup.ts",
      "./src/renderer/test-component-setup.tsx",
    ],
    typecheck: {
      tsconfig: "./tsconfig.web.json",
    },
    coverage: {
      provider: "v8",
      reporter: ["text", "json", "html"],
      include: ["src/**"],
    },
    projects: [
      {
        test: {
          name: "unit", // main process unit tests
          include: ["src/main/**/*.test.ts", "src/main/**/*.test.tsx"],
          globals: true,
          environment: "node",
        },
        define: {
          // Unit tests might reference proxy functions, so provide dummy values
          __PROXY_CMD__: JSON.stringify("dummy-proxy-command"),
          __PROXY_ORIGIN__: JSON.stringify("http://dummy-origin"),
        },
      },
      {
        test: {
          name: "component",
          include: ["src/renderer/**/*.test.ts", "src/renderer/**/*.test.tsx"],
          globals: true,
          environment: "jsdom",
        },
      },
      {
        test: {
          name: "integration", // Integration tests that may use testcontainers
          include: ["integration_tests/**/*.test.ts"],
          setupFiles: ["integration_tests/setup.ts"],
          globals: true,
        },
      },
      {
        test: {
          name: "server", // Tests that require a running server
          include: ["server_tests/**/*.test.ts"],
          globals: true,
          testTimeout: 30000, // 30s default timeout
        },
        define: {
          __PROXY_CMD__: JSON.stringify(sdProxyCmd),
          __PROXY_ORIGIN__: JSON.stringify("http://127.0.0.1:8081"),
        },
      },
    ],
  },
  resolve: {
    alias: {
      "@renderer": resolve("src/renderer"),
    },
  },
});
