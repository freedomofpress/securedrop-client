import { expect, afterEach } from "vitest";
import { cleanup } from "@testing-library/react";
import * as matchers from "@testing-library/jest-dom/matchers";
import * as vitestAxeMatchers from "vitest-axe/matchers";
import "vitest-axe/extend-expect";

// extends Vitest's expect with jest-dom matchers
expect.extend(matchers);

// extend Vitest's expect with axe a11y matchers
expect.extend(vitestAxeMatchers);

// runs a cleanup after each test case (e.g. clearing jsdom)
afterEach(() => {
  cleanup();
});
