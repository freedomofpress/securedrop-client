/// <reference types="vitest" />
/// <reference types="vite/client" />

import type { TestingLibraryMatchers } from "@testing-library/jest-dom/matchers";
import type { AxeMatchers } from "vitest-axe/matchers";

declare module "vitest" {
  interface Assertion<T = unknown>
    extends jest.Matchers<void>, TestingLibraryMatchers<T, void>, AxeMatchers {}
  interface AsymmetricMatchersContaining
    extends
      jest.Matchers<void>,
      TestingLibraryMatchers<unknown, void>,
      AxeMatchers {}
}
