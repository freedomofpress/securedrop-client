import { screen } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { describe, expect, it, vi } from "vitest";
import Toolbar from "./Toolbar";
import {
  renderWithProviders,
  testMemoization,
} from "../../../../test-component-setup";
import type { filterOption } from "./Toolbar";

describe("Toolbar filter dropdown", () => {
  const baseProps = {
    allSelected: false,
    selectedCount: 0,
    totalCount: 4,
    onSelectAll: vi.fn(),
    onBulkDelete: vi.fn(),
    searchTerm: "",
    filter: "all" as filterOption,
    sortedAsc: false,
    dropdownOpen: false,
    onSearchChange: vi.fn(),
    onFilterChange: vi.fn(),
    onToggleSort: vi.fn(),
    onDropdownOpenChange: vi.fn(),
  };

  it("offers a Drafts filter", async () => {
    const onFilterChange = vi.fn();
    renderWithProviders(
      <Toolbar {...baseProps} onFilterChange={onFilterChange} />,
    );

    await userEvent.click(screen.getByTestId("filter-dropdown"));
    await userEvent.click(screen.getByText("Drafts"));

    expect(onFilterChange).toHaveBeenCalledWith("drafts");
  });

  it("shows Drafts as the label when the drafts filter is active", () => {
    renderWithProviders(<Toolbar {...baseProps} filter="drafts" />);

    expect(screen.getByTestId("filter-dropdown").textContent).toContain(
      "Drafts",
    );
  });
});

describe("Toolbar Component Memoization", () => {
  const mockOnSelectAll = vi.fn();
  const mockOnBulkDelete = vi.fn();
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
