import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import { resolve } from "path";

export default defineConfig({
  plugins: [react()],
  test: {
    globals: true,
    environment: "jsdom",
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
  },
  resolve: {
    alias: {
      "@renderer": resolve("src/renderer"),
    },
  },
});
