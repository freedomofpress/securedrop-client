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
          name: "unit", // Unit and component tests
          include: ["src/**/*.test.ts", "src/**/*.test.tsx"],
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
    ],
  },
  resolve: {
    alias: {
      "@renderer": resolve("src/renderer"),
    },
  },
});
