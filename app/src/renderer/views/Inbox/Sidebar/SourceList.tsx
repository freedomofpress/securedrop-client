import { useState } from "react";
import { useNavigate, useParams } from "react-router";
import { Checkbox, Button, Dropdown, Input, Tooltip } from "antd";
import {
  DeleteOutlined,
  MailOutlined,
  SortAscendingOutlined,
  SortDescendingOutlined,
  DownOutlined,
  SearchOutlined,
} from "@ant-design/icons";
import { useTranslation } from "react-i18next";

import Source from "./SourceList/Source";
import { useDebounce, useInfiniteScroll } from "../../../hooks";

type filterOption = "all" | "read" | "unread" | "starred" | "unstarred";

function SourceList() {
  const { t } = useTranslation("Sidebar");
  const navigate = useNavigate();
  const { sourceUuid: activeSourceUuid } = useParams<{ sourceUuid?: string }>();

  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [allSelected, setAllSelected] = useState(false);
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<filterOption>("all");
  const [searchTerm, setSearchTerm] = useState("");

  // Debounce search term to avoid too many queries
  const debouncedSearchTerm = useDebounce(searchTerm, 300);

  // Use infinite scroll hook
  const { sources, loading, hasMore, totalCount, containerRef } =
    useInfiniteScroll({
      searchTerm: debouncedSearchTerm,
      filter,
      sortedAsc,
    });

  // Handle select all checkbox
  const handleSelectAll = (checked: boolean) => {
    if (checked) {
      setSelectedSources(new Set(sources.map((source) => source.uuid)));
      setAllSelected(true);
    } else {
      setSelectedSources(new Set());
      setAllSelected(false);
    }
  };

  // Handle individual source selection
  const handleSourceSelect = (sourceId: string, checked: boolean) => {
    const newSelection = new Set(selectedSources);
    if (checked) {
      newSelection.add(sourceId);
    } else {
      newSelection.delete(sourceId);
    }
    setSelectedSources(newSelection);
    setAllSelected(newSelection.size === sources.length);
  };

  // Handle starring/unstarring a source
  const handleToggleStar = async (
    sourceId: string,
    currentlyStarred: boolean,
  ) => {
    // TODO: Implement API call to toggle star status
    // For now, just log the action
    console.log(`Toggle star for source ${sourceId}: ${!currentlyStarred}`);
  };

  // Handle source click to navigate to source route
  const handleSourceClick = (sourceId: string) => {
    if (activeSourceUuid === sourceId) {
      // If already active, navigate back to inbox home
      navigate("/");
      return;
    }
    // Navigate to the source route
    navigate(`/source/${sourceId}`);
  };

  const handleBulkDelete = () => {
    console.log("Delete selected sources:", selectedSources);
  };

  const handleBulkToggleRead = () => {
    console.log("Toggle read status for selected sources:", selectedSources);
  };

  const handleToggleSort = () => {
    setSortedAsc(!sortedAsc);
    // Clear selections when sort changes
    setSelectedSources(new Set());
    setAllSelected(false);
  };

  const handleFilterChange = (newFilter: filterOption) => {
    setFilter(newFilter);
    // Clear selections when filter changes
    setSelectedSources(new Set());
    setAllSelected(false);
  };

  const dropdownItems = [
    {
      key: "all",
      label: t("sourcelist.filters.all"),
      onClick: () => handleFilterChange("all"),
    },
    {
      key: "read",
      label: t("sourcelist.filters.read"),
      onClick: () => handleFilterChange("read"),
    },
    {
      key: "unread",
      label: t("sourcelist.filters.unread"),
      onClick: () => handleFilterChange("unread"),
    },
    {
      key: "starred",
      label: t("sourcelist.filters.starred"),
      onClick: () => handleFilterChange("starred"),
    },
    {
      key: "unstarred",
      label: t("sourcelist.filters.unstarred"),
      onClick: () => handleFilterChange("unstarred"),
    },
  ];

  return (
    <div className="flex-1 flex flex-col min-h-0">
      {/* Header with select all and action buttons */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b flex-shrink-0">
        <div className="flex items-center justify-between gap-2 min-w-0">
          <div className="flex items-center gap-2 flex-shrink-0">
            {/* Select all checkbox */}
            <Checkbox
              checked={allSelected}
              indeterminate={
                selectedSources.size > 0 &&
                selectedSources.size < sources.length
              }
              onChange={(e) => handleSelectAll(e.target.checked)}
              data-testid="select-all-checkbox"
            />

            {/* Only display action buttons if sources are selected */}
            {selectedSources.size > 0 && (
              <>
                <Tooltip title={t("sourcelist.actions.bulkDelete")}>
                  <Button
                    type="text"
                    icon={<DeleteOutlined />}
                    onClick={handleBulkDelete}
                    data-testid="bulk-delete-button"
                  />
                </Tooltip>
                <Tooltip title={t("sourcelist.actions.bulkToggleRead")}>
                  <Button
                    type="text"
                    icon={<MailOutlined />}
                    onClick={handleBulkToggleRead}
                    data-testid="bulk-toggle-read-button"
                  />
                </Tooltip>
              </>
            )}
          </div>

          <Input
            placeholder={t("sourcelist.search.placeholder")}
            prefix={<SearchOutlined />}
            value={searchTerm}
            onChange={(e) => setSearchTerm(e.target.value)}
            className="flex-1 min-w-0 max-w-xs"
            allowClear
          />

          <div className="flex items-center gap-1 flex-shrink-0">
            <Dropdown menu={{ items: dropdownItems }} trigger={["click"]}>
              <Button type="text" data-testid="filter-dropdown">
                {dropdownItems.find((item) => item.key === filter)?.label}{" "}
                <DownOutlined />
              </Button>
            </Dropdown>

            <Tooltip title={t("sourcelist.sort.tooltip")}>
              <Button
                type="text"
                icon={
                  sortedAsc ? (
                    <SortDescendingOutlined />
                  ) : (
                    <SortAscendingOutlined />
                  )
                }
                onClick={handleToggleSort}
                data-testid="sort-button"
              />
            </Tooltip>
          </div>
        </div>
      </div>

      {/* Sources list */}
      <div className="flex-1 min-h-0 relative">
        <div ref={containerRef} className="absolute inset-0 overflow-y-auto">
          {sources.map((source) => {
            const isSelected = selectedSources.has(source.uuid);
            const isActive = activeSourceUuid === source.uuid;

            return (
              <Source
                key={source.uuid}
                source={source}
                isSelected={isSelected}
                isActive={isActive}
                onSelect={handleSourceSelect}
                onToggleStar={handleToggleStar}
                onClick={handleSourceClick}
              />
            );
          })}

          {/* Loading indicator at the bottom when loading more */}
          {loading && (
            <div className="text-center py-2 text-sm text-gray-500">
              {t("sourcelist.loading")}
            </div>
          )}

          {/* Show total count and load status */}
          {!loading && sources.length > 0 && (
            <div className="text-center py-2 text-sm text-gray-500">
              {t("sourcelist.showing", {
                count: sources.length,
                total: totalCount,
              })}
            </div>
          )}

          {/* Empty state */}
          {!loading && sources.length === 0 && (
            <div className="flex items-center justify-center h-full text-gray-500">
              {t("sourcelist.noSources")}
            </div>
          )}
        </div>
      </div>
    </div>
  );
}

export default SourceList;
