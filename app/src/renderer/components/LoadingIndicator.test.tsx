import { describe, it } from "vitest";
import LoadingIndicator from "./LoadingIndicator";
import { testMemoization } from "../test-component-setup";

describe("LoadingIndicator Component Memoization", () => {
  const cases: Array<[Record<string, never>, number]> = [
    // Initial render
    [{}, 1],
    // Same props (no props) - should not re-render
    [{}, 1],
    // Another identical render - should not re-render
    [{}, 1],
  ];

  it(
    "should handle memoization correctly",
    testMemoization(LoadingIndicator, cases),
  );
});
