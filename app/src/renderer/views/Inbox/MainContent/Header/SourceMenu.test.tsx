import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import SourceMenu from "./SourceMenu";
import {
  testMemoization,
  renderWithProviders,
} from "../../../../test-component-setup";
import type { SourceWithItems } from "../../../../../types";

describe("SourceMenu Component", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  const mockSourceWithItems: SourceWithItems = {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      journalist_designation: "durian smoothie",
      last_updated: "2024-01-15T10:30:00Z",
      public_key: "-----BEGIN PGP PUBLIC KEY BLOCK-----\n...\n-----END-----",
      uuid: "source-1",
      is_seen: true,
      has_attachment: false,
    },
    items: [],
  };

  describe("Memoization", () => {
    const cases: Array<
      [
        {
          sourceWithItems: SourceWithItems;
        },
        number,
      ]
    > = [
      // Initial render
      [
        {
          sourceWithItems: mockSourceWithItems,
        },
        1,
      ],
      // Same props - should not re-render
      [
        {
          sourceWithItems: mockSourceWithItems,
        },
        1,
      ],
      // Change sourceWithItems - should re-render
      [
        {
          sourceWithItems: {
            ...mockSourceWithItems,
            data: {
              ...mockSourceWithItems.data,
              journalist_designation: "different designation",
            },
          },
        },
        2,
      ],
    ];

    it(
      "should handle memoization correctly",
      testMemoization(SourceMenu, cases),
    );
  });
  describe("Source with no conversation items", () => {
    it("renders the menu with disabled export options", async () => {
      renderWithProviders(<SourceMenu sourceWithItems={mockSourceWithItems} />);
      const menuButton = screen.getByRole("button");
      expect(menuButton).toBeInTheDocument();
      await userEvent.click(menuButton);

      await waitFor(() => {
        // menu should appear
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        // there should be an Export Transcript option, but it should be disabled
        const exportTranscriptItem = screen.getByRole("menuitem", {
          name: /export transcript/i,
        });
        expect(exportTranscriptItem).toBeInTheDocument();
        // expect(exportTranscriptItem).toBeDisabled(); doesn't work here, you need to test for the ant class :(
        expect(exportTranscriptItem).toHaveClass(
          "ant-dropdown-menu-item-disabled",
        );

        // there should be a Print Transcript option, but it should also be disabled
        const printTranscriptItem = screen.getByRole("menuitem", {
          name: /print transcript/i,
        });
        expect(printTranscriptItem).toBeInTheDocument();
        expect(printTranscriptItem).toHaveClass(
          "ant-dropdown-menu-item-disabled",
        );
      });
    });
  });
  describe("Source with at least one conversation item", () => {
    const s: SourceWithItems = {
      uuid: "source-1",
      data: {
        uuid: "source-1",
        journalist_designation: "test source",
        is_starred: false,
        is_seen: false,
        has_attachment: false,
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
            interaction_count: 1,
          },
          fetch_progress: 1024,
          fetch_status: 3,
        },
      ],
    };
    it("renders the menu with enabled export options", async () => {
      renderWithProviders(<SourceMenu sourceWithItems={s} />);
      const menuButton = screen.getByRole("button");
      expect(menuButton).toBeInTheDocument();
      await userEvent.click(menuButton);

      await waitFor(() => {
        // menu should appear
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        // there is an Export Transcript option, and it is enabled and clickable
        const exportTranscriptItem = screen.getByRole("menuitem", {
          name: /export transcript/i,
        });
        expect(exportTranscriptItem).toBeInTheDocument();
        expect(exportTranscriptItem).not.toHaveClass(
          "ant-dropdown-menu-item-disabled",
        );

        // there is a Print Transcript option, and it is also disabled
        const printTranscriptItem = screen.getByRole("menuitem", {
          name: /print transcript/i,
        });
        expect(printTranscriptItem).toBeInTheDocument();
        expect(printTranscriptItem).not.toHaveClass(
          "ant-dropdown-menu-item-disabled",
        );
      });
    });

    it("opens the Export Wizard when Export Transcript is clicked ", async () => {
      renderWithProviders(<SourceMenu sourceWithItems={s} />);
      const menuButton = screen.getByRole("button");
      expect(menuButton).toBeInTheDocument();
      await userEvent.click(menuButton);

      await waitFor(() => {
        // menu should appear
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        // there is an Export Transcript option, and it is enabled and clickable
        const exportItem = screen.getByRole("menuitem", {
          name: /export transcript/i,
        });
        expect(exportItem).toBeInTheDocument();
      });

      const exportItem = screen.getByRole("menuitem", {
        name: /export transcript/i,
      });
      await userEvent.click(exportItem);
      await waitFor(() => {
        expect(screen.getByText("Preparing to export.")).toBeInTheDocument();
      });
    });
    it("opens the Print Wizard when Print Transcript is clicked ", async () => {
      renderWithProviders(<SourceMenu sourceWithItems={s} />);
      const menuButton = screen.getByRole("button");
      expect(menuButton).toBeInTheDocument();
      await userEvent.click(menuButton);

      await waitFor(() => {
        // menu should appear
        const menu = screen.getByRole("menu");
        expect(menu).toBeInTheDocument();

        // there is an Print Transcript option, and it is enabled and clickable
        const printItem = screen.getByRole("menuitem", {
          name: /print transcript/i,
        });
        expect(printItem).toBeInTheDocument();
      });

      const printItem = screen.getByRole("menuitem", {
        name: /print transcript/i,
      });
      await userEvent.click(printItem);
      await waitFor(() => {
        expect(screen.getByText("Preparing to print.")).toBeInTheDocument();
        expect(screen.getByText("source transcript")).toBeInTheDocument();
      });
    });
  });
});
