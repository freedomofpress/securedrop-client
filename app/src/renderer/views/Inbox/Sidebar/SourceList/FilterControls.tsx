import { useMemo } from "react";
import { Button, Dropdown, Input, Tooltip } from "antd";
import {
  Search,
  CalendarArrowDown,
  CalendarArrowUp,
  ChevronDown,
  ChevronUp,
} from "lucide-react";
import { useTranslation } from "react-i18next";
import "./FilterControls.css";

type filterOption = "all" | "read" | "unread" | "starred" | "unstarred";

interface FilterControlsProps {
  searchTerm: string;
  filter: filterOption;
  sortedAsc: boolean;
  dropdownOpen: boolean;
  onSearchChange: (e: React.ChangeEvent<HTMLInputElement>) => void;
  onFilterChange: (newFilter: filterOption) => void;
  onToggleSort: () => void;
  onDropdownOpenChange: (open: boolean) => void;
}

function FilterControls({
  searchTerm,
  filter,
  sortedAsc,
  dropdownOpen,
  onSearchChange,
  onFilterChange,
  onToggleSort,
  onDropdownOpenChange,
}: FilterControlsProps) {
  const { t } = useTranslation("Sidebar");

  const dropdownItems = useMemo(
    () => [
      {
        key: "all",
        label: t("sourcelist.filters.all"),
        onClick: () => onFilterChange("all"),
      },
      {
        key: "read",
        label: t("sourcelist.filters.read"),
        onClick: () => onFilterChange("read"),
      },
      {
        key: "unread",
        label: t("sourcelist.filters.unread"),
        onClick: () => onFilterChange("unread"),
      },
      {
        key: "starred",
        label: t("sourcelist.filters.starred"),
        onClick: () => onFilterChange("starred"),
      },
      {
        key: "unstarred",
        label: t("sourcelist.filters.unstarred"),
        onClick: () => onFilterChange("unstarred"),
      },
    ],
    [t, onFilterChange],
  );

  return (
    <>
      <Input
        placeholder={t("sourcelist.search.placeholder")}
        prefix={<Search size={18} />}
        value={searchTerm}
        onChange={onSearchChange}
        className="flex-1 min-w-0 max-w-xs"
        allowClear
      />

      <div className="flex items-center gap-1 flex-shrink-0">
        <Dropdown
          className={`sd-filter-${filter}`}
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
    </>
  );
}

export default FilterControls;
export type { filterOption };
