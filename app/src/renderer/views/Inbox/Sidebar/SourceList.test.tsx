import { screen, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import userEvent from "@testing-library/user-event";
import SourceList from "./SourceList";
import type { Source as SourceType } from "../../../../types";
import type { SourceProps } from "./SourceList/Source";
import { renderWithProviders } from "../../../test-component-setup";

// Mock the Source component to simplify testing the main Sources component logic
vi.mock("./SourceList/Source", () => ({
  default: ({
    source,
    isSelected,
    isActive,
    onSelect,
    onToggleStar,
    onClick,
  }: SourceProps) => (
    <div
      data-testid={`source-${source.uuid}`}
      data-selected={isSelected}
      data-active={isActive}
      onClick={() => onClick(source.uuid)}
    >
      <input
        type="checkbox"
        data-testid={`source-checkbox-${source.uuid}`}
        checked={isSelected}
        onChange={(e) => onSelect(source.uuid, e.target.checked)}
      />
      <button
        data-testid={`star-button-${source.uuid}`}
        onClick={(e) => {
          e.stopPropagation();
          onToggleStar(source.uuid, source.data.is_starred);
        }}
      >
        {source.data.is_starred ? "star" : "no-star"}
      </button>
      <span data-testid={`source-designation-${source.uuid}`}>
        {source.data.journalist_designation}
      </span>
    </div>
  ),
}));

describe("Sources Component", () => {
  const mockGetSources = vi.fn();
  const mockGetSourcesCount = vi.fn();

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

    // Mock electronAPI
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    (window as any).electronAPI = {
      getSources: mockGetSources,
      getSourcesCount: mockGetSourcesCount,
    };

    // Default mock implementation - simulate pagination
    mockGetSources.mockImplementation(({ limit = 100, offset = 0 } = {}) => {
      const startIndex = offset;
      const endIndex = Math.min(startIndex + limit, mockSources.length);
      return Promise.resolve(mockSources.slice(startIndex, endIndex));
    });
    mockGetSourcesCount.mockResolvedValue(mockSources.length);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("Default behavior", () => {
    it("displays all sources by default", async () => {
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-3")).toBeInTheDocument();
        expect(screen.getByTestId("source-source-4")).toBeInTheDocument();
      });
    });

    it("loads sources on mount", async () => {
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledTimes(1);
      });
    });
  });

  describe("Action buttons visibility", () => {
    it("hides action buttons when no checkboxes are checked", async () => {
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
    it("filters sources by designation when search term is entered", async () => {
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByPlaceholderText("Search by name");
      await userEvent.type(searchInput, "alice");

      // Only Alice Wonderland should be visible
      expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-2")).not.toBeInTheDocument();
      expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
      expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
    });

    it("filters sources case-insensitively", async () => {
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByPlaceholderText("Search by name");
      await userEvent.type(searchInput, "BOB");

      // Bob Builder should be visible (case-insensitive search)
      expect(screen.queryByTestId("source-source-1")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
      expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
    });

    it("shows all sources when search is cleared", async () => {
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      const searchInput = screen.getByPlaceholderText("Search by name");
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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

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
      renderWithProviders(<SourceList />);

      await waitFor(() => {
        expect(screen.getByTestId("source-source-1")).toBeInTheDocument();
      });

      // Search for "b" (should match bob builder and charlie chaplin)
      const searchInput = screen.getByPlaceholderText("Search by name");
      await userEvent.type(searchInput, "b");

      // Filter to starred (should only show bob builder since charlie isn't starred)
      const filterButton = screen.getByTestId("filter-dropdown");
      await userEvent.click(filterButton);
      await userEvent.click(screen.getByText("Starred"));

      // Only Bob Builder should be visible (matches search "b" and is starred)
      expect(screen.queryByTestId("source-source-1")).not.toBeInTheDocument();
      expect(screen.getByTestId("source-source-2")).toBeInTheDocument();
      expect(screen.queryByTestId("source-source-3")).not.toBeInTheDocument();
      expect(screen.queryByTestId("source-source-4")).not.toBeInTheDocument();
    });

    it("maintains sort order when filtering", async () => {
      renderWithProviders(<SourceList />);

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
});
