import { describe, it } from "vitest";
import Conversation from "./Conversation";
import { testMemoization } from "../../../test-component-setup";
import type { ItemUpdate, SourceWithItems } from "../../../../types";

describe("Conversation Component Memoization", () => {
  const mockSourceWithItems: SourceWithItems = {
    uuid: "source-1",
    data: {
      uuid: "source-1",
      journalist_designation: "test source",
      is_starred: false,
      last_updated: "2025-01-15T10:00:00Z",
      public_key: "test-public-key",
      fingerprint: "test-fingerprint",
    },
    items: [
      {
        uuid: "item-1",
        data: {
          kind: "message",
          uuid: "item-1",
          source: "source-1",
          size: 1024,
          seen_by: [],
          is_read: false,
        },
        fetch_progress: 1024,
        fetch_status: 3,
      },
    ],
  };

  const mockOnUpdate: (_: ItemUpdate) => void = vi.fn();

  const cases: Array<
    [
      {
        sourceWithItems: SourceWithItems | null;
        onItemUpdate: (_: ItemUpdate) => void;
      },
      number,
    ]
  > = [
    // Initial render with source
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 1],
    // Same props - should not re-render
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 1],
    // Null source - should re-render
    [{ sourceWithItems: null, onItemUpdate: mockOnUpdate }, 2],
    // Back to same source - should re-render
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 3],
    // Different source - should re-render
    [
      {
        sourceWithItems: {
          ...mockSourceWithItems,
          uuid: "source-2",
          data: { ...mockSourceWithItems.data, uuid: "source-2" },
        },
        onItemUpdate: mockOnUpdate,
      },
      4,
    ],
  ];

  it(
    "should handle memoization correctly",
    testMemoization(Conversation, cases),
  );
});
