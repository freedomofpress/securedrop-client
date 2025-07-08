import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";

export default defineConfig({
  plugins: [react()],
  test: {
    coverage: {
      provider: "v8",
      reporter: ["text", "json", "html"],
      include: ["src/**"],
    },
    environment: "jsdom",
    projects: [
      {
        test: {
          name: "unit",
          include: ["tests/**/*.test.ts"],
          setupFiles: "./src/setupTests.ts",
          globals: true,
        },
      },
      {
        test: {
          name: "integration",
          include: ["integration_tests/**/*.test.ts"],
          setupFiles: ["integration_tests/setup.ts"],
          globals: true,
        },
      },
    ],
  },
});
