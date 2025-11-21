import { describe, it } from "vitest";
import Header from "./Header";
import { testMemoization } from "../../../test-component-setup";
import type { SourceWithItems } from "../../../../types";

describe("Header Component Memoization", () => {
  const mockSourceWithItems: SourceWithItems = {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      journalist_designation: "multiplicative conditionality",
      last_updated: "2024-01-15T10:30:00Z",
      public_key: "-----BEGIN PGP PUBLIC KEY BLOCK-----\n...\n-----END-----",
      uuid: "source-1",
      is_seen: true,
      has_attachment: false,
    },
    items: [],
  };

  const cases: Array<
    [
      {
        sourceUuid?: string;
        loading: boolean;
        sourceWithItems: SourceWithItems | null;
      },
      number,
    ]
  > = [
    // Initial render
    [
      {
        sourceUuid: "source-1",
        loading: false,
        sourceWithItems: mockSourceWithItems,
      },
      1,
    ],
    // Same props - should not re-render
    [
      {
        sourceUuid: "source-1",
        loading: false,
        sourceWithItems: mockSourceWithItems,
      },
      1,
    ],
    // Change loading state - should re-render
    [
      {
        sourceUuid: "source-1",
        loading: true,
        sourceWithItems: mockSourceWithItems,
      },
      2,
    ],
    // Change sourceUuid - should re-render
    [
      {
        sourceUuid: "source-2",
        loading: true,
        sourceWithItems: mockSourceWithItems,
      },
      3,
    ],
    // Change sourceWithItems - should re-render
    [
      {
        sourceUuid: "source-2",
        loading: true,
        sourceWithItems: {
          ...mockSourceWithItems,
          data: {
            ...mockSourceWithItems.data,
            journalist_designation: "different designation",
          },
        },
      },
      4,
    ],
  ];

  it("should handle memoization correctly", testMemoization(Header, cases));
});
