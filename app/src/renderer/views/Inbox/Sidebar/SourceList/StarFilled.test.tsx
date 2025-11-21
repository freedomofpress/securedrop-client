import { describe, it } from "vitest";
import StarFilled from "./StarFilled";
import { testMemoization } from "../../../../test-component-setup";

describe("StarFilled Component Memoization", () => {
  const cases: Array<
    [{ size?: number; color?: string; className?: string }, number]
  > = [
    // Initial render with defaults
    [{}, 1],
    // Same props - should not re-render
    [{}, 1],
    // Change size - should re-render
    [{ size: 24 }, 2],
    // Change color - should re-render
    [{ size: 24, color: "#ff0000" }, 3],
    // Change className - should re-render
    [{ size: 24, color: "#ff0000", className: "test-class" }, 4],
    // Back to defaults - should re-render
    [{}, 5],
  ];

  it("should handle memoization correctly", testMemoization(StarFilled, cases));
});
