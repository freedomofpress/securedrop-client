import { describe, it } from "vitest";
import Message from "./Message";
import { testMemoization } from "../../../../../test-component-setup";
import type { Item } from "../../../../../../types";

describe("Message Component Memoization", () => {
  const mockItem: Item = {
    uuid: "item-1",
    data: {
      uuid: "item-1",
      kind: "message",
      seen_by: [],
      size: 512,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    plaintext: "Hello, this is a message",
  };
  const mockOnUpdate = vi.fn();

  const cases: Array<
    [{ item: Item; designation: string; onUpdate: () => void }, number]
  > = [
    // Initial render
    [{ item: mockItem, designation: "Test Source", onUpdate: mockOnUpdate }, 1],
    // Same props - should not re-render
    [{ item: mockItem, designation: "Test Source", onUpdate: mockOnUpdate }, 1],
    // Change designation - should re-render
    [
      {
        item: mockItem,
        designation: "Different Source",
        onUpdate: mockOnUpdate,
      },
      2,
    ],
    // Change item plaintext - should re-render
    [
      {
        item: { ...mockItem, plaintext: "Different message" },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
      },
      3,
    ],
    // Change to encrypted (no plaintext) - should re-render
    [
      {
        item: { ...mockItem, plaintext: undefined },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
      },
      4,
    ],
  ];

  it("should handle memoization correctly", testMemoization(Message, cases));
});
