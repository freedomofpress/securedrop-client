import { useState, useEffect, useMemo, useCallback, useRef } from "react";
import { useParams } from "react-router";
import { FixedSizeList as List } from "react-window";

import type { Source as SourceType } from "../../../../types";
import Source from "./SourceList/Source";
import LoadingIndicator from "../../../components/LoadingIndicator";
import { useDebounce } from "../../../hooks";
import Toolbar, { type filterOption } from "./SourceList/Toolbar";

function SourceList() {
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
    ({ index, style }: { index: number; style: React.CSSProperties }) => {
      const source = filteredSources[index];
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
    ],
  );

  return (
    <div className="flex-1 flex flex-col min-h-0">
      {/* Toolbar with controls and actions */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b flex-shrink-0">
        <Toolbar
          allSelected={allSelected}
          selectedCount={selectedSources.size}
          totalCount={sources.length}
          onSelectAll={handleSelectAll}
          onBulkDelete={handleBulkDelete}
          onBulkToggleRead={handleBulkToggleRead}
          searchTerm={searchTerm}
          filter={filter}
          sortedAsc={sortedAsc}
          dropdownOpen={dropdownOpen}
          onSearchChange={handleSearchChange}
          onFilterChange={handleFilterChange}
          onToggleSort={handleToggleSort}
          onDropdownOpenChange={setDropdownOpen}
        />
      </div>

      {/* Sources list */}
      <div ref={containerRef} className="flex-1 min-h-0 relative">
        {loading && <LoadingIndicator />}
        <div className="absolute inset-0">
          <List
            height={containerHeight}
            width="100%"
            itemCount={filteredSources.length}
            itemSize={72} // Height of each source item
            className="select-none"
          >
            {ItemRenderer}
          </List>
        </div>
      </div>
    </div>
  );
}

export default SourceList;
