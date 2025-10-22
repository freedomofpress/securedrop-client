import { useMemo, memo } from "react";
import { Button, Dropdown, Input, Tooltip, Checkbox } from "antd";
import {
  Search,
  CalendarArrowDown,
  CalendarArrowUp,
  ChevronDown,
  ChevronUp,
  Trash,
  Mail,
} from "lucide-react";
import { useTranslation } from "react-i18next";

type filterOption = "all" | "read" | "unread" | "starred" | "unstarred";

interface ToolbarProps {
  // Select all state
  allSelected: boolean;
  selectedCount: number;
  totalCount: number;
  onSelectAll: (checked: boolean) => void;

  // Action handlers
  onBulkDelete: () => void;
  onBulkToggleRead: () => void;

  // Filter controls
  searchTerm: string;
  filter: filterOption;
  sortedAsc: boolean;
  dropdownOpen: boolean;
  onSearchChange: (e: React.ChangeEvent<HTMLInputElement>) => void;
  onFilterChange: (newFilter: filterOption) => void;
  onToggleSort: () => void;
  onDropdownOpenChange: (open: boolean) => void;
}

const Toolbar = memo(function Toolbar({
  allSelected,
  selectedCount,
  totalCount,
  onSelectAll,
  onBulkDelete,
  onBulkToggleRead,
  searchTerm,
  filter,
  sortedAsc,
  dropdownOpen,
  onSearchChange,
  onFilterChange,
  onToggleSort,
  onDropdownOpenChange,
}: ToolbarProps) {
  const { t } = useTranslation("Sidebar");

  const dropdownItems = useMemo(
    () => [
      {
        key: "all",
        label: t("sourcelist.filters.all"),
        onClick: () => onFilterChange("all"),
        "data-testid": "filter-all",
      },
      {
        key: "read",
        label: t("sourcelist.filters.read"),
        onClick: () => onFilterChange("read"),
        "data-testid": "filter-read",
      },
      {
        key: "unread",
        label: t("sourcelist.filters.unread"),
        onClick: () => onFilterChange("unread"),
        "data-testid": "filter-unread",
      },
      {
        key: "starred",
        label: t("sourcelist.filters.starred"),
        onClick: () => onFilterChange("starred"),
        "data-testid": "filter-starred",
      },
      {
        key: "unstarred",
        label: t("sourcelist.filters.unstarred"),
        onClick: () => onFilterChange("unstarred"),
        "data-testid": "filter-unstarred",
      },
    ],
    [t, onFilterChange],
  );

  return (
    <div className="flex items-center justify-between gap-2 min-w-0">
      <div className="flex items-center gap-1 flex-shrink-0">
        {/* Select all checkbox */}
        <Checkbox
          checked={allSelected}
          indeterminate={selectedCount > 0 && selectedCount < totalCount}
          onChange={(e) => onSelectAll(e.target.checked)}
          data-testid="select-all-checkbox"
        />

        {/* Only display action buttons if sources are selected */}
        {selectedCount > 0 && (
          <>
            <Tooltip title={t("sourcelist.actions.bulkDelete")}>
              <Button
                type="text"
                icon={<Trash size={18} />}
                onClick={onBulkDelete}
                data-testid="bulk-delete-button"
              />
            </Tooltip>
            <Tooltip title={t("sourcelist.actions.bulkToggleRead")}>
              <Button
                type="text"
                icon={<Mail size={18} />}
                onClick={onBulkToggleRead}
                data-testid="bulk-toggle-read-button"
              />
            </Tooltip>
          </>
        )}
      </div>

      <Input
        placeholder={t("sourcelist.search.placeholder")}
        prefix={<Search size={18} />}
        value={searchTerm}
        data-testid="source-search-input"
        onChange={onSearchChange}
        className="flex-1 min-w-0 max-w-xs"
        allowClear
      />

      <div className="flex items-center gap-1 flex-shrink-0">
        <Dropdown
          menu={{ items: dropdownItems }}
          trigger={["click"]}
          onOpenChange={onDropdownOpenChange}
        >
          <Button type="text" data-testid="filter-dropdown">
            {dropdownItems.find((item) => item.key === filter)?.label}{" "}
            {dropdownOpen ? <ChevronUp size={18} /> : <ChevronDown size={18} />}
          </Button>
        </Dropdown>

        <Tooltip title={t("sourcelist.sort.tooltip")}>
          <Button
            type="text"
            icon={
              sortedAsc ? (
                <CalendarArrowUp size={18} />
              ) : (
                <CalendarArrowDown size={18} />
              )
            }
            onClick={onToggleSort}
            data-testid="sort-button"
          />
        </Tooltip>
      </div>
    </div>
  );
});

export default Toolbar;
export type { filterOption };
