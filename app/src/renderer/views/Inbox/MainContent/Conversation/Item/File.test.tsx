import { describe, it, vi } from "vitest";
import File from "./File";
import { testMemoization } from "../../../../../test-component-setup";
import { FetchStatus, type Item } from "../../../../../../types";

describe("File Component Memoization", () => {
  const mockOnUpdate = vi.fn();
  const mockOnDelete = vi.fn();
  const mockItem: Item = {
    uuid: "item-1",
    data: {
      uuid: "item-1",
      kind: "file",
      seen_by: [],
      size: 1024,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    plaintext: null,
    filename: null,
    fetch_progress: null,
    decrypted_size: null,
    fetch_status: FetchStatus.Initial,
  };

  const cases: Array<
    [
      {
        item: Item;
        designation: string;
        onUpdate: () => void;
        onDelete: () => void;
      },
      number,
    ]
  > = [
    // Initial render
    [
      {
        item: mockItem,
        designation: "Test Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      1,
    ],
    // Same props - should not re-render
    [
      {
        item: mockItem,
        designation: "Test Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      1,
    ],
    // Change designation - should re-render
    [
      {
        item: mockItem,
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      2,
    ],
    // Change item - should re-render
    [
      {
        item: { ...mockItem, uuid: "item-2" },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      3,
    ],
    // Change fetch_status - should re-render
    [
      {
        item: {
          ...mockItem,
          uuid: "item-2",
          fetch_status: FetchStatus.Complete,
        },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      4,
    ],
    [
      {
        item: {
          ...mockItem,
          uuid: "item-2",
          fetch_status: FetchStatus.ScheduledDeletion,
        },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      5,
    ],
  ];

  it("should handle memoization correctly", testMemoization(File, cases));
});
