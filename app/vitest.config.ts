import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import { resolve } from "path";

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
          // Unit tests run in the main/backend process, not renderer
          __RENDERER_ONLY__: "false",
        },
      },
      {
        test: {
          name: "component",
          include: ["src/renderer/**/*.test.ts", "src/renderer/**/*.test.tsx"],
          globals: true,
          environment: "jsdom",
        },
        define: {
          // Component tests run in the renderer process
          __RENDERER_ONLY__: "true",
        },
      },
      {
        test: {
          name: "integration", // Integration tests that may use testcontainers
          include: ["integration_tests/**/*.test.ts"],
          setupFiles: ["integration_tests/setup.ts"],
          globals: true,
        },
        define: {
          __RENDERER_ONLY__: "false",
        },
      },
      {
        test: {
          name: "server", // Tests that require a running server
          include: ["server_tests/**/*.test.ts"],
          globals: true,
          testTimeout: 60000, // 60 seconds default timeout for individual tests
          // Run test files sequentially to ensure isolated server instances don't conflict
          // Tests within a file still run sequentially by default
          pool: "forks",
          poolOptions: {
            forks: {
              singleFork: true, // Run one file at a time
            },
          },
        },
        define: {
          __RENDERER_ONLY__: "false",
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
