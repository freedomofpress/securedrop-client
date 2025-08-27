import { describe, it, vi } from "vitest";
import Toolbar from "./Toolbar";
import { testMemoization } from "../../../../test-component-setup";
import type { filterOption } from "./Toolbar";

describe("Toolbar Component Memoization", () => {
  const mockOnSelectAll = vi.fn();
  const mockOnBulkDelete = vi.fn();
  const mockOnBulkToggleRead = vi.fn();
  const mockOnSearchChange = vi.fn();
  const mockOnFilterChange = vi.fn();
  const mockOnToggleSort = vi.fn();
  const mockOnDropdownOpenChange = vi.fn();

  const baseProps = {
    allSelected: false,
    selectedCount: 0,
    totalCount: 4,
    onSelectAll: mockOnSelectAll,
    onBulkDelete: mockOnBulkDelete,
    onBulkToggleRead: mockOnBulkToggleRead,
    searchTerm: "",
    filter: "all" as filterOption,
    sortedAsc: false,
    dropdownOpen: false,
    onSearchChange: mockOnSearchChange,
    onFilterChange: mockOnFilterChange,
    onToggleSort: mockOnToggleSort,
    onDropdownOpenChange: mockOnDropdownOpenChange,
  };

  const cases: Array<[typeof baseProps, number]> = [
    // Initial render
    [baseProps, 1],
    // Same props - should not re-render
    [baseProps, 1],
    // Change allSelected - should re-render
    [{ ...baseProps, allSelected: true }, 2],
    // Change selectedCount - should re-render
    [{ ...baseProps, allSelected: true, selectedCount: 2 }, 3],
    // Change searchTerm - should re-render
    [
      {
        ...baseProps,
        allSelected: true,
        selectedCount: 2,
        searchTerm: "test search",
      },
      4,
    ],
    // Change filter - should re-render
    [
      {
        ...baseProps,
        allSelected: true,
        selectedCount: 2,
        searchTerm: "test search",
        filter: "unread",
      },
      5,
    ],
    // Change sortedAsc - should re-render
    [
      {
        ...baseProps,
        allSelected: true,
        selectedCount: 2,
        searchTerm: "test search",
        filter: "unread",
        sortedAsc: true,
      },
      6,
    ],
    // Change dropdownOpen - should re-render
    [
      {
        ...baseProps,
        allSelected: true,
        selectedCount: 2,
        searchTerm: "test search",
        filter: "unread",
        sortedAsc: true,
        dropdownOpen: true,
      },
      7,
    ],
    // Back to initial props - should re-render
    [baseProps, 8],
  ];

  it("should handle memoization correctly", testMemoization(Toolbar, cases));
});
