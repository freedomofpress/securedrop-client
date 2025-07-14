import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import { resolve } from "path";

export default defineConfig({
  plugins: [react()],
  test: {
    globals: true,
    environment: "jsdom",
    setupFiles: ["./src/test-setup.ts"],
    typecheck: {
      tsconfig: "./tsconfig.web.json",
    },
  },
  resolve: {
    alias: {
      "@renderer": resolve("src/renderer"),
    },
  },
});
