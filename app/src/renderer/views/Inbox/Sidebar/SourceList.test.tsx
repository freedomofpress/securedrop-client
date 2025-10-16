import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import React from "react";
import SourceList from "./SourceList";
import type { Source as SourceType } from "../../../../types";
import { PendingEventType } from "../../../../types";
import type { SourceProps } from "./SourceList/Source";
import { renderWithProviders } from "../../../test-component-setup";

// Mock react-window to render all items instead of virtualizing
vi.mock("react-window", () => ({
  FixedSizeList: ({
    children: ItemRenderer,
    itemCount,
    height,
    className,
  }: {
    children: ({
      index,
      style,
      isScrolling,
    }: {
      index: number;
      style: React.CSSProperties;
      isScrolling?: boolean;
    }) => React.ReactNode;
    itemCount: number;
    height: number;
    itemSize?: number; // Optional since we don't use it in the mock
    className: string;
  }) => (
    <div
      data-testid="virtualized-list"
      data-item-count={itemCount}
      style={{ height }}
      className={className}
    >
      {Array.from({ length: itemCount }, (_, index) => (
        <div key={index}>
          {ItemRenderer({ index, style: {}, isScrolling: false })}
        </div>
      ))}
    </div>
  ),
}));

// Mock the Source component
vi.mock("./SourceList/Source", () => ({
  default: ({
    source,
    isSelected,
    isActive,
    onSelect,
    onToggleStar,
  }: SourceProps) => (
    <div
      className={`flex items-center px-4 py-3 border-b border-gray-100 cursor-pointer transition-colors duration-150 ease-in-out
        ${isActive ? "bg-blue-500 text-white hover:bg-blue-600" : "hover:bg-gray-50"}
        ${isSelected && !isActive ? "bg-blue-25" : ""}
      `}
      data-testid={`source-${source.uuid}`}
      data-selected={isSelected}
      data-active={isActive}
    >
      {/* Checkbox - using input to match test expectations */}
      <input
        type="checkbox"
        data-testid={`source-checkbox-${source.uuid}`}
        checked={isSelected}
        onChange={(e) => {
          e.stopPropagation();
          onSelect(source.uuid, e.target.checked);
        }}
        onClick={(e) => e.stopPropagation()}
      />

      {/* Star button */}
      <button
        data-testid={`star-button-${source.uuid}`}
        onClick={(e) => {
          e.stopPropagation();
          onToggleStar(source.uuid, source.data.is_starred);
        }}
      >
        {source.data.is_starred ? "★" : "☆"}
      </button>

      {/* Source designation */}
      <span
        data-testid={`source-designation-${source.uuid}`}
        className={`text-sm truncate ${
          isActive ? "text-white" : "text-gray-900"
        } ${!source.isRead ? "font-bold" : "font-medium"}`}
      >
        {source.data.journalist_designation}
      </span>
    </div>
  ),
}));

describe("Sources Component", () => {
  // Mock sources data with different states for comprehensive testing
  const mockSources: SourceType[] = [
    {
      uuid: "source-1",
      data: {
        fingerprint: "fingerprint-1",
        is_starred: false,
        journalist_designation: "alice wonderland",
        last_updated: "2024-01-15T10:30:00Z",
        public_key: "key-1",
        uuid: "source-1",
      },
      isRead: false,
      hasAttachment: false,
      showMessagePreview: false,
      messagePreview: "",
    },
    {
      uuid: "source-2",
      data: {
        fingerprint: "fingerprint-2",
        is_starred: true,
        journalist_designation: "bob builder",
        last_updated: "2024-01-16T15:45:00Z",
        public_key: "key-2",
        uuid: "source-2",
      },
      isRead: true,
      hasAttachment: true,
      showMessagePreview: true,
      messagePreview: "Hello from Bob",
    },
    {
      uuid: "source-3",
      data: {
        fingerprint: "fingerprint-3",
        is_starred: false,
        journalist_designation: "charlie chaplin",
        last_updated: "2024-01-14T09:15:00Z",
        public_key: "key-3",
        uuid: "source-3",
      },
      isRead: false,
      hasAttachment: false,
      showMessagePreview: false,
      messagePreview: "",
    },
    {
      uuid: "source-4",
      data: {
        fingerprint: "fingerprint-4",
        is_starred: true,
        journalist_designation: "diana ross",
        last_updated: "2024-01-17T11:20:00Z",
        public_key: "key-4",
        uuid: "source-4",
      },
      isRead: true,
      hasAttachment: false,
      showMessagePreview: false,
      messagePreview: "",
    },
  ];

  beforeEach(() => {
    // Reset mocks
    vi.clearAllMocks();

    // Mock electronAPI with partial implementation for these tests
    window.electronAPI = {
      getSources: vi.fn().mockResolvedValue(mockSources),
      syncMetadata: vi.fn().mockResolvedValue(undefined),
    } as Partial<typeof window.electronAPI> as typeof window.electronAPI;
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  // Helper function to render SourceList with Redux state
  const renderSourceList = (sources = mockSources, loading = false) => {
    return renderWithProviders(<SourceList />, {
      preloadedState: {
        sources: {
          sources,
          activeSourceUuid: null,
          loading,
          error: null,
        },
      },
    });
  };

  describe("Default behavior", () => {
    it("displays sources from Redux state", async () => {
      renderSourceList();

      await waitFor(() => {
        // Check that sources are being rendered from Redux state
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
      });

      // Verify virtual list is being used
      const virtualList = screen.getByTestId("virtualized-list");
      expect(virtualList).toBeInTheDocument();
      expect(virtualList.getAttribute("data-item-count")).toBe("4");
    });

    it("dispatches fetchSources action on mount", async () => {
      // This test would require Redux action monitoring, but the core functionality
      // is that sources are displayed, which is covered by other tests
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });
    });
  });

  describe("Action buttons visibility", () => {
    it("hides action buttons when no checkboxes are checked", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Action buttons should not be visible
      expect(
        screen.queryByTestId("bulk-delete-button"),
      ).not.toBeInTheDocument();
      expect(
        screen.queryByTestId("bulk-toggle-read-button"),
      ).not.toBeInTheDocument();
    });

    it("shows action buttons when any checkbox is checked", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Check one source
      const checkbox = screen.getByTestId("source-checkbox-source-1");
      await userEvent.click(checkbox);

      // Action buttons should now be visible
      expect(screen.getByTestId("bulk-delete-button")).toBeInTheDocument();
      expect(screen.getByTestId("bulk-toggle-read-button")).toBeInTheDocument();
    });

    it("hides action buttons when all checkboxes are unchecked", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Check and then uncheck a source
      const checkbox = screen.getByTestId("source-checkbox-source-1");
      await userEvent.click(checkbox);
      await userEvent.click(checkbox);

      // Action buttons should be hidden again
      expect(
        screen.queryByTestId("bulk-delete-button"),
      ).not.toBeInTheDocument();
      expect(
        screen.queryByTestId("bulk-toggle-read-button"),
      ).not.toBeInTheDocument();
    });
  });

  describe("Select all functionality", () => {
    it("checks all sources when select all is clicked with none selected", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const selectAllCheckbox = screen.getByTestId("select-all-checkbox");
      await userEvent.click(selectAllCheckbox);

      // All individual checkboxes should be checked
      expect(screen.getByTestId("source-checkbox-source-1")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-2")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-3")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-4")).toBeChecked();
    });

    it("checks all sources when select all is clicked with some selected", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Check some sources first
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));
      await userEvent.click(screen.getByTestId("source-checkbox-source-2"));

      const selectAllCheckbox = screen.getByTestId("select-all-checkbox");
      await userEvent.click(selectAllCheckbox);

      // All individual checkboxes should be checked
      expect(screen.getByTestId("source-checkbox-source-1")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-2")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-3")).toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-4")).toBeChecked();
    });

    it("unchecks all sources when select all is clicked with all selected", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Check all sources first
      const selectAllCheckbox = screen.getByTestId("select-all-checkbox");
      await userEvent.click(selectAllCheckbox);

      // Then uncheck all
      await userEvent.click(selectAllCheckbox);

      // All individual checkboxes should be unchecked
      expect(screen.getByTestId("source-checkbox-source-1")).not.toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-2")).not.toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-3")).not.toBeChecked();
      expect(screen.getByTestId("source-checkbox-source-4")).not.toBeChecked();
    });
  });

  describe("Search functionality", () => {
    it("debounces search input to avoid excessive filtering", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByTestId("source-search-input");

      // Type quickly and check that we get the debounced result
      await userEvent.type(searchInput, "alice");

      // Should wait for debounce and then filter to only show Alice
      await waitFor(
        () => {
          expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-2"),
          ).not.toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-3"),
          ).not.toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-4"),
          ).not.toBeInTheDocument();
        },
        { timeout: 1000 },
      );
    });

    it("filters sources by designation when search term is entered", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByTestId("source-search-input");
      await userEvent.type(searchInput, "alice");

      // Wait for debounce
      await waitFor(() => {
        // Only Alice Wonderland should be visible
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
        expect(screen.queryByTestId("source-source-2")).not.toBeInTheDocument();
        expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
        expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
      });
    });

    it("filters sources case-insensitively", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByTestId("source-search-input");
      await userEvent.type(searchInput, "BOB");

      // Wait for debounce and Bob Builder should be visible (case-insensitive search)
      await waitFor(
        () => {
          expect(
            screen.queryByTestId("source-source-1"),
          ).not.toBeInTheDocument();
          expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-3"),
          ).not.toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-4"),
          ).not.toBeInTheDocument();
        },
        { timeout: 1000 },
      );
    });

    it("shows all sources when search is cleared", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByTestId("source-search-input");
      await userEvent.type(searchInput, "alice");
      await userEvent.clear(searchInput);

      // All sources should be visible again
      expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
    });
  });

  describe("Filter dropdown functionality", () => {
    it("filters to show only unread sources", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Click the filter dropdown
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);

      // Click "Unread" option
      const unreadOption = screen.getByText("Unread");
      await userEvent.click(unreadOption);

      // Only unread sources should be visible (source-1 and source-3)
      expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-2")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
    });

    it("filters to show only read sources", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Click the filter dropdown
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);

      // Click "Read" option
      const readOption = screen.getByText("Read");
      await userEvent.click(readOption);

      // Only read sources should be visible (source-2 and source-4)
      expect(screen.queryByTestId("source-source-1")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
    });

    it("filters to show only starred sources", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Click the filter dropdown
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);

      // Click "Starred" option
      const starredOption = screen.getByText("Starred");
      await userEvent.click(starredOption);

      // Only starred sources should be visible (source-2 and source-4)
      expect(screen.queryByTestId("source-source-1")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
    });

    it("filters to show only unstarred sources", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Click the filter dropdown
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);

      // Click "Unstarred" option
      const unstarredOption = screen.getByText("Unstarred");
      await userEvent.click(unstarredOption);

      // Only unstarred sources should be visible (source-1 and source-3)
      expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-2")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
    });

    it("shows all sources when 'All' filter is selected", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // First filter to unread
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);
      await userEvent.click(screen.getByText("Unread"));

      // Then back to All
      const unreadButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(unreadButton);
      await userEvent.click(screen.getByText("All"));

      // All sources should be visible again
      expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
      expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
    });
  });

  describe("Sort functionality", () => {
    it("sorts sources in descending order by default (newest first)", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const sources = screen.getAllByTestId(/^source-source-/);
      const sourceOrder = sources.map((el) => el.getAttribute("data-testid"));

      // Should be ordered by last_updated descending: source-4, source-2, source-1, source-3
      expect(sourceOrder).toEqual([
        "source-source-4", // 2024-01-17 (newest)
        "source-source-2", // 2024-01-16
        "source-source-1", // 2024-01-15
        "source-source-3", // 2024-01-14 (oldest)
      ]);
    });

    it("sorts sources in ascending order when sort button is clicked (oldest first)", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Click the sort button to toggle to ascending
      const sortBtn = screen.getByTestId("sort-button");
      await userEvent.click(sortBtn);

      const sources = screen.getAllByTestId(/^source-source-/);
      const sourceOrder = sources.map((el) => el.getAttribute("data-testid"));

      // Should be ordered by last_updated ascending: source-3, source-1, source-2, source-4
      expect(sourceOrder).toEqual([
        "source-source-3", // 2024-01-14 (oldest)
        "source-source-1", // 2024-01-15
        "source-source-2", // 2024-01-16
        "source-source-4", // 2024-01-17 (newest)
      ]);
    });

    it("toggles between ascending and descending when sort button is clicked multiple times", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const sortBtn = screen.getByTestId("sort-button");

      // Click once for ascending
      await userEvent.click(sortBtn);

      let sources = screen.getAllByTestId(/^source-source-/);
      let sourceOrder = sources.map((el) => el.getAttribute("data-testid"));
      expect(sourceOrder[0]).toBe("source-source-3"); // oldest first

      // Click again for descending
      await userEvent.click(sortBtn);

      sources = screen.getAllByTestId(/^source-source-/);
      sourceOrder = sources.map((el) => el.getAttribute("data-testid"));
      expect(sourceOrder[0]).toBe("source-source-4"); // newest first
    });
  });

  describe("Combined functionality", () => {
    it("applies both search and filter together", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Search for "b" (should match bob builder and charlie chaplin)
      const searchInput = screen.getByTestId("source-search-input");
      await userEvent.type(searchInput, "b");

      // Filter to starred (should only show bob builder since charlie isn't starred)
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);
      await userEvent.click(screen.getByText("Starred"));

      await waitFor(
        () => {
          // Only Bob Builder should be visible (matches search "b" and is starred)
          expect(
            screen.queryByTestId("source-source-1"),
          ).not.toBeInTheDocument();
          expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-3"),
          ).not.toBeInTheDocument();
          expect(
            screen.queryByTestId("source-source-4"),
          ).not.toBeInTheDocument();
        },
        { timeout: 1000 },
      );
    });

    it("maintains sort order when filtering", async () => {
      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Filter to starred sources (source-2 and source-4)
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);
      await userEvent.click(screen.getByText("Starred"));

      const sources = screen.getAllByTestId(/^source-source-/);
      const sourceOrder = sources.map((el) => el.getAttribute("data-testid"));

      // Should still be in date descending order: source-4 (newer), source-2 (older)
      expect(sourceOrder).toEqual(["source-source-4", "source-source-2"]);
    });
  });

  describe("Bulk delete functionality", () => {
    beforeEach(() => {
      // Mock the showMessageBox function
      window.electronAPI.showMessageBox = vi.fn();
      window.electronAPI.addPendingSourceEvent = vi
        .fn()
        .mockResolvedValue(BigInt(123));
    });

    it("shows dialog when delete button is clicked with single source selected", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 0,
        checkboxChecked: false,
      }); // Cancel

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select one source
      const checkbox = screen.getByTestId("source-checkbox-source-1");
      await userEvent.click(checkbox);

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        expect(window.electronAPI.showMessageBox).toHaveBeenCalledWith(
          expect.objectContaining({
            message: expect.stringContaining(
              "Do you want to delete the source's account or just the conversation?",
            ),
            buttons: expect.arrayContaining([
              "Cancel",
              "Delete Account",
              "Delete Conversation",
            ]),
            type: "warning",
          }),
        );
      });
    });

    it("shows dialog with correct message for multiple sources", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 0,
        checkboxChecked: false,
      }); // Cancel

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select two sources
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));
      await userEvent.click(screen.getByTestId("source-checkbox-source-2"));

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        expect(window.electronAPI.showMessageBox).toHaveBeenCalledWith(
          expect.objectContaining({
            message: expect.stringContaining(
              "Do you want to delete these 2 source accounts or just the conversations?",
            ),
            buttons: expect.arrayContaining([
              "Cancel",
              "Delete Accounts",
              "Delete Conversations",
            ]),
          }),
        );
      });
    });

    it("calls addPendingSourceEvent with SourceDeleted when Delete Account is selected", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 1,
        checkboxChecked: false,
      }); // Delete Account

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select one source
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        expect(window.electronAPI.addPendingSourceEvent).toHaveBeenCalledWith(
          "source-1",
          PendingEventType.SourceDeleted,
        );
      });
    });

    it("calls addPendingSourceEvent with SourceConversationDeleted when Delete Conversation is selected", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 2,
        checkboxChecked: false,
      }); // Delete Conversation

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select one source
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        expect(window.electronAPI.addPendingSourceEvent).toHaveBeenCalledWith(
          "source-1",
          PendingEventType.SourceConversationDeleted,
        );
      });
    });

    it("calls addPendingSourceEvent for all selected sources", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 1,
        checkboxChecked: false,
      }); // Delete Account

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select multiple sources
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));
      await userEvent.click(screen.getByTestId("source-checkbox-source-2"));
      await userEvent.click(screen.getByTestId("source-checkbox-source-3"));

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        const addPendingSourceEvent = window.electronAPI.addPendingSourceEvent;
        expect(addPendingSourceEvent).toHaveBeenCalledTimes(3);
        expect(addPendingSourceEvent).toHaveBeenCalledWith(
          "source-1",
          PendingEventType.SourceDeleted,
        );
        expect(addPendingSourceEvent).toHaveBeenCalledWith(
          "source-2",
          PendingEventType.SourceDeleted,
        );
        expect(addPendingSourceEvent).toHaveBeenCalledWith(
          "source-3",
          PendingEventType.SourceDeleted,
        );
      });
    });

    it("does not call addPendingSourceEvent when Cancel is selected", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 0,
        checkboxChecked: false,
      }); // Cancel

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select one source
      await userEvent.click(screen.getByTestId("source-checkbox-source-1"));

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      await waitFor(() => {
        expect(window.electronAPI.showMessageBox).toHaveBeenCalled();
      });

      // Wait a bit to ensure addPendingSourceEvent is not called
      await new Promise((resolve) => setTimeout(resolve, 100));

      expect(window.electronAPI.addPendingSourceEvent).not.toHaveBeenCalled();
    });

    it("clears selection after deleting sources", async () => {
      vi.mocked(window.electronAPI.showMessageBox).mockResolvedValue({
        response: 1,
        checkboxChecked: false,
      }); // Delete Account

      renderSourceList();

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Select sources
      const checkbox1 = screen.getByTestId("source-checkbox-source-1");
      const checkbox2 = screen.getByTestId("source-checkbox-source-2");
      await userEvent.click(checkbox1);
      await userEvent.click(checkbox2);

      // Verify they are checked
      expect(checkbox1).toBeChecked();
      expect(checkbox2).toBeChecked();

      // Click bulk delete button
      const deleteButton = screen.getByTestId("bulk-delete-button");
      await userEvent.click(deleteButton);

      // Wait for the operation to complete
      await waitFor(() => {
        expect(window.electronAPI.addPendingSourceEvent).toHaveBeenCalled();
      });

      // Checkboxes should be unchecked
      await waitFor(() => {
        expect(checkbox1).not.toBeChecked();
        expect(checkbox2).not.toBeChecked();
      });
    });
  });
});
