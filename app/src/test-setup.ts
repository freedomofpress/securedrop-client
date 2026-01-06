import { expect, afterEach } from "vitest";
import { cleanup } from "@testing-library/react";
import * as matchers from "@testing-library/jest-dom/matchers";

// extends Vitest's expect with jest-dom matchers
expect.extend(matchers);

// Polyfill ResizeObserver for jsdom (used by antd v6 components)
class ResizeObserver {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  constructor(_callback: any) {}
  observe() {}
  unobserve() {}
  disconnect() {}
}

// Ensure global availability across all runtimes
const globalTarget = globalThis as typeof globalThis &
  Partial<Window & typeof global>;

if (!globalTarget.ResizeObserver) {
  globalTarget.ResizeObserver = ResizeObserver;
}

// JSDOM may expose both window and global; set both explicitly for safety
if (typeof window !== "undefined" && !window.ResizeObserver) {
  window.ResizeObserver = ResizeObserver;
}

// runs a cleanup after each test case (e.g. clearing jsdom)
afterEach(() => {
  cleanup();
});
