import { describe, it } from "vitest";
import Avatar from "./Avatar";
import { testMemoization } from "../test-component-setup";

describe("Avatar Component Memoization", () => {
  const cases: Array<[{ designation: string; isActive?: boolean }, number]> = [
    // Initial render
    [{ designation: "Cool Source", isActive: false }, 1],
    // Same props - should not re-render
    [{ designation: "Cool Source", isActive: false }, 1],
    // Change designation - should re-render
    [{ designation: "Different Source", isActive: false }, 2],
    // Change isActive - should re-render
    [{ designation: "Different Source", isActive: true }, 3],
    // Back to same props as step 3 - should re-render (props changed from step 4)
    [{ designation: "Different Source", isActive: false }, 4],
  ];

  it("should handle memoization correctly", testMemoization(Avatar, cases));
});
