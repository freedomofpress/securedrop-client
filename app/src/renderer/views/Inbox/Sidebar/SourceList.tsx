import { useState, useEffect, useMemo, useCallback, useRef } from "react";
import { useNavigate, useParams } from "react-router";
import { FixedSizeList as List } from "react-window";
import { Checkbox, Button, Dropdown, Input, Tooltip } from "antd";
import {
  Trash,
  Mail,
  Search,
  CalendarArrowDown,
  CalendarArrowUp,
  ChevronDown,
  ChevronUp,
} from "lucide-react";
import { useTranslation } from "react-i18next";

import type { Source as SourceType } from "../../../../types";
import Source from "./SourceList/Source";
import LoadingIndicator from "../../../components/LoadingIndicator";
import { useDebounce } from "../../../hooks";

type filterOption = "all" | "read" | "unread" | "starred" | "unstarred";

function SourceList() {
  const { t } = useTranslation("Sidebar");
  const navigate = useNavigate();
  const { sourceUuid: activeSourceUuid } = useParams<{ sourceUuid?: string }>();

  const [loading, setLoading] = useState(false);
  const [sources, setSources] = useState<SourceType[]>([]);
  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [allSelected, setAllSelected] = useState(false);
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<filterOption>("all");
  const [searchTerm, setSearchTerm] = useState("");
  const [dropdownOpen, setDropdownOpen] = useState(false);
  const [containerHeight, setContainerHeight] = useState(1000); // Larger default for testing
  const containerRef = useRef<HTMLDivElement>(null);

  // Debounce search term to avoid excessive filtering
  const debouncedSearchTerm = useDebounce(searchTerm, 300);

  useEffect(() => {
    const fetchSources = async () => {
      setLoading(true);
      const sources = await window.electronAPI.getSources();
      setSources(sources);
      setLoading(false);
    };
    fetchSources();
  }, []);

  // Calculate container height for react-window
  useEffect(() => {
    const updateHeight = () => {
      if (containerRef.current) {
        const rect = containerRef.current.getBoundingClientRect();
        setContainerHeight(rect.height);
      }
    };

    updateHeight();
    window.addEventListener("resize", updateHeight);
    return () => window.removeEventListener("resize", updateHeight);
  }, []);

  // Handle select all checkbox
  const handleSelectAll = useCallback(
    (checked: boolean) => {
      if (checked) {
        setSelectedSources(new Set(sources.map((source) => source.uuid)));
        setAllSelected(true);
      } else {
        setSelectedSources(new Set());
        setAllSelected(false);
      }
    },
    [sources],
  );

  // Handle individual source selection
  const handleSourceSelect = useCallback(
    (sourceId: string, checked: boolean) => {
      setSelectedSources((prev) => {
        const newSelection = new Set(prev);
        if (checked) {
          newSelection.add(sourceId);
        } else {
          newSelection.delete(sourceId);
        }
        setAllSelected(newSelection.size === sources.length);
        return newSelection;
      });
    },
    [sources.length],
  );

  // Handle starring/unstarring a source
  const handleToggleStar = useCallback(
    async (sourceId: string, currentlyStarred: boolean) => {
      // TODO: Implement API call to toggle star status

      // Update local state optimistically
      setSources((prevSources) =>
        prevSources.map((source) =>
          source.uuid === sourceId
            ? {
                ...source,
                data: { ...source.data, is_starred: !currentlyStarred },
              }
            : source,
        ),
      );
    },
    [],
  );

  // Handle source click to navigate to source route
  const handleSourceClick = useCallback(
    (sourceId: string) => {
      if (activeSourceUuid === sourceId) {
        // If already active, navigate back to inbox home
        navigate("/");
        return;
      }
      // Navigate to the source route
      navigate(`/source/${sourceId}`);
    },
    [activeSourceUuid, navigate],
  );

  const handleBulkDelete = useCallback(() => {
    console.log("Delete selected sources:", selectedSources);
  }, [selectedSources]);

  const handleBulkToggleRead = useCallback(() => {
    console.log("Toggle read status for selected sources:", selectedSources);
  }, [selectedSources]);

  const handleToggleSort = useCallback(() => {
    setSortedAsc((prev) => !prev);
  }, []);

  const handleFilterChange = useCallback((newFilter: filterOption) => {
    setFilter(newFilter);
  }, []);

  const handleSearchChange = useCallback(
    (e: React.ChangeEvent<HTMLInputElement>) => {
      setSearchTerm(e.target.value);
    },
    [],
  );

  // Filter and sort sources based on the selected filter and sort order
  const filteredSources = useMemo(() => {
    return sources
      .filter((source) => {
        // First filter by search term
        const matchesSearch = source.data.journalist_designation
          .toLowerCase()
          .includes(debouncedSearchTerm.toLowerCase());

        if (!matchesSearch) {
          return false;
        }

        // Then filter by the selected filter option
        switch (filter) {
          case "unread":
            return !source.isRead;
          case "read":
            return source.isRead;
          case "starred":
            return source.data.is_starred;
          case "unstarred":
            return !source.data.is_starred;
          case "all":
          default:
            return true; // "all" filter shows everything
        }
      })
      .sort((a, b) => {
        const dateA = new Date(a.data.last_updated).getTime();
        const dateB = new Date(b.data.last_updated).getTime();

        if (sortedAsc) {
          return dateA - dateB; // Ascending: oldest first
        } else {
          return dateB - dateA; // Descending: newest first
        }
      });
  }, [sources, debouncedSearchTerm, filter, sortedAsc]);

  // Item renderer for react-window
  const ItemRenderer = useCallback(
    ({
      index,
      style,
      isScrolling,
    }: {
      index: number;
      style: React.CSSProperties;
      isScrolling?: boolean;
    }) => {
      const source = filteredSources[index];

      // Show placeholder while scrolling
      if (isScrolling) {
        return (
          <div
            style={style}
            className="sd-bg-primary sd-border-secondary border-b p-4 flex items-center"
          >
            <div className="w-6 h-6 bg-gray-200 rounded animate-pulse mr-3"></div>
            <div className="flex-1">
              <div className="h-4 bg-gray-200 rounded animate-pulse mb-2 w-3/4"></div>
              <div className="h-3 bg-gray-200 rounded animate-pulse w-1/2"></div>
            </div>
          </div>
        );
      }

      const isSelected = selectedSources.has(source.uuid);
      const isActive = activeSourceUuid === source.uuid;

      return (
        <div style={style}>
          <Source
            source={source}
            isSelected={isSelected}
            isActive={isActive}
            onSelect={handleSourceSelect}
            onToggleStar={handleToggleStar}
            onClick={handleSourceClick}
          />
        </div>
      );
    },
    [
      filteredSources,
      selectedSources,
      activeSourceUuid,
      handleSourceSelect,
      handleToggleStar,
      handleSourceClick,
    ],
  );

  const dropdownItems = useMemo(
    () => [
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
    ],
    [t, handleFilterChange],
  );

  return (
    <div className="flex-1 flex flex-col min-h-0">
      {/* Header with select all and action buttons */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b flex-shrink-0">
        <div className="flex items-center justify-between gap-2 min-w-0">
          <div className="flex items-center gap-1 flex-shrink-0">
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
                    icon={<Trash size={18} />}
                    onClick={handleBulkDelete}
                    data-testid="bulk-delete-button"
                  />
                </Tooltip>
                <Tooltip title={t("sourcelist.actions.bulkToggleRead")}>
                  <Button
                    type="text"
                    icon={<Mail size={18} />}
                    onClick={handleBulkToggleRead}
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
            onChange={handleSearchChange}
            className="flex-1 min-w-0 max-w-xs"
            allowClear
          />

          <div className="flex items-center gap-1 flex-shrink-0">
            <Dropdown
              menu={{ items: dropdownItems }}
              trigger={["click"]}
              onOpenChange={setDropdownOpen}
            >
              <Button type="text" data-testid="filter-dropdown">
                {dropdownItems.find((item) => item.key === filter)?.label}{" "}
                {dropdownOpen ? (
                  <ChevronUp size={18} />
                ) : (
                  <ChevronDown size={18} />
                )}
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
                onClick={handleToggleSort}
                data-testid="sort-button"
              />
            </Tooltip>
          </div>
        </div>
      </div>

      {/* Sources list */}
      <div ref={containerRef} className="flex-1 min-h-0 relative">
        {loading && <LoadingIndicator />}
        <div className="absolute inset-0">
          <List
            height={containerHeight}
            itemCount={filteredSources.length}
            itemSize={72} // Height of each source item
            className="select-none"
            useIsScrolling
          >
            {ItemRenderer}
          </List>
        </div>
      </div>
    </div>
  );
}

export default SourceList;
