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
    environment: 'jsdom',
    globals: true,
    setupFiles: './src/setupTests.ts',
  },
});
