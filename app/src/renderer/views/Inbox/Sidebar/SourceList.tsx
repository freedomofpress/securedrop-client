import { useState, useEffect, useMemo, useCallback } from "react";
import { useParams } from "react-router";
import { List, useListRef } from "react-window";

import type { RowComponentProps } from "react-window";
import Source from "./SourceList/Source";
import { useDebounce, useAppDispatch, useAppSelector } from "../../../hooks";
import {
  fetchSources,
  selectSources,
} from "../../../features/sources/sourcesSlice";
import {
  openDeleteModal,
  selectDeleteModalOpen,
  selectLastDeletedSources,
} from "../../../features/deleteModal/deleteModalSlice";
import Toolbar, { type filterOption } from "./SourceList/Toolbar";
import Counts from "./SourceList/Counts";
import {
  PendingEventType,
  SearchResult,
  type Source as SourceType,
} from "../../../../types";
import { useSidebarShortcuts, useShortcut } from "../../../shortcuts";
import type { FocusedPanel } from "../../Inbox";

interface SourceRowProps {
  filteredSources: SourceType[];
  selectedSources: Set<string>;
  activeSourceUuid: string | undefined;
  onSelect: (sourceId: string, checked: boolean) => void;
  onToggleStar: (sourceId: string, currentlyStarred: boolean) => void;
}

// nosemgrep: react-component-missing-memo -- memo is ineffective here because shared rowProps (selectedSources) change reference on every selection; the child <Source> is already memo'd
function SourceRow({
  index,
  style,
  filteredSources,
  selectedSources,
  activeSourceUuid,
  onSelect,
  onToggleStar,
}: RowComponentProps<SourceRowProps>) {
  const source = filteredSources[index];
  const isSelected = selectedSources.has(source.uuid);
  const isActive = activeSourceUuid === source.uuid;

  return (
    <div style={style}>
      <Source
        source={source}
        isSelected={isSelected}
        isActive={isActive}
        onSelect={onSelect}
        onToggleStar={onToggleStar}
      />
    </div>
  );
}

function SourceList({ focusedPanel }: { focusedPanel: FocusedPanel }) {
  const { sourceUuid: activeSourceUuid } = useParams<{ sourceUuid?: string }>();
  const dispatch = useAppDispatch();
  const listRef = useListRef(null);

  const sources = useAppSelector(selectSources);
  const deleteModalOpen = useAppSelector(selectDeleteModalOpen);
  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<filterOption>("all");
  const [searchTerm, setSearchTerm] = useState("");
  const [dropdownOpen, setDropdownOpen] = useState(false);

  // Debounce search term to avoid excessive filtering
  const debouncedSearchTerm = useDebounce(searchTerm, 300);
  const [searchResults, setSearchResults] = useState<SearchResult[] | null>(
    null,
  );

  useEffect(() => {
    dispatch(fetchSources());
  }, [dispatch]);

  // Only search once we have at least 3 characters.
  const isSearchActive = debouncedSearchTerm.trim().length >= 3;

  // When the search goes inactive (fewer than 3 characters), clear any stale
  // results during render rather than in the effect below, so we don't commit a
  // frame still showing outdated search results.
  const [prevIsSearchActive, setPrevIsSearchActive] = useState(isSearchActive);
  if (isSearchActive !== prevIsSearchActive) {
    setPrevIsSearchActive(isSearchActive);
    if (!isSearchActive) {
      setSearchResults(null);
    }
  }

  // Perform the search via IPC when the term changes or sources update. This is
  // a genuine async side effect, so it stays in an effect.
  useEffect(() => {
    if (!isSearchActive) {
      return;
    }

    let cancelled = false;

    const performSearch = async () => {
      try {
        const results = await window.electronAPI.search(debouncedSearchTerm);
        if (!cancelled) {
          setSearchResults(results);
        }
      } catch (error) {
        console.error("Failed to search sources:", error);
        if (!cancelled) {
          setSearchResults(null);
        }
      }
    };

    void performSearch();

    return () => {
      cancelled = true;
    };
  }, [debouncedSearchTerm, sources, isSearchActive]);

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
        return newSelection;
      });
    },
    [],
  );

  // Handle starring/unstarring a source
  const handleToggleStar = useCallback(
    async (sourceId: string, currentlyStarred: boolean) => {
      // Add pending event
      const eventType = currentlyStarred
        ? PendingEventType.Unstarred
        : PendingEventType.Starred;
      try {
        await window.electronAPI.addPendingSourceEvent(sourceId, eventType);

        // Update local state immediately with projected changes
        dispatch(fetchSources());
      } catch (error) {
        console.error("Failed to toggle source star state:", error);
      }
    },
    [dispatch],
  );

  // Bulk delete button: opens the shared delete modal for the currently
  // checked sources. Deleted sources are dropped from the selection reactively
  // by the selection-pruning effect once they leave the store.
  const handleBulkDelete = useCallback(() => {
    dispatch(openDeleteModal(Array.from(selectedSources)));
  }, [dispatch, selectedSources]);

  // Keyboard shortcut: Ctrl+Delete deletes the current source
  useShortcut(
    "deleteSource",
    () => {
      if (!deleteModalOpen && activeSourceUuid) {
        dispatch(openDeleteModal([activeSourceUuid]));
      }
    },
    undefined,
    [dispatch, deleteModalOpen, activeSourceUuid],
  );

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
    // Map search results to source objects
    let searchedSources: SourceType[] = [];
    if (searchResults !== null) {
      // Dedupe by sourceUuid, keeping the highest-ranked result per source
      const seen = new Set<string>();

      for (const sr of searchResults) {
        if (seen.has(sr.sourceUuid)) {
          continue;
        }
        seen.add(sr.sourceUuid);
        const source = sources[sr.sourceUuid];
        if (!source) {
          continue;
        }
        if (
          sr.type === "message" ||
          sr.type === "reply" ||
          sr.type === "file"
        ) {
          searchedSources.push({
            ...source,
            messagePreview: { kind: sr.type, plaintext: sr.snippet },
          });
        } else {
          searchedSources.push(source);
        }
      }
    } else {
      searchedSources = Object.values(sources);
    }

    return searchedSources
      .filter((source) => {
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
            return true;
        }
      })
      .sort((a, b) => {
        const dateA = new Date(a.data.last_updated).getTime();
        const dateB = new Date(b.data.last_updated).getTime();

        if (sortedAsc) {
          return dateA - dateB;
        } else {
          return dateB - dateA;
        }
      });
  }, [sources, searchResults, filter, sortedAsc]);

  const allSelected = useMemo(
    () =>
      filteredSources.length > 0 &&
      filteredSources.every((s) => selectedSources.has(s.uuid)),
    [filteredSources, selectedSources],
  );

  const totalSourceCount = Object.keys(sources).length;

  // Handle select all checkbox
  const handleSelectAll = useCallback(
    (checked: boolean) => {
      if (checked) {
        setSelectedSources(
          new Set(filteredSources.map((source) => source.uuid)),
        );
      } else {
        setSelectedSources(new Set());
      }
    },
    [filteredSources],
  );

  // Selection-pruning: whenever the visible sources change — because of a
  // filter, a search, or because sources were deleted and left the store —
  // trim the selection down to only sources that are still visible.
  //
  // We adjust the selection during render (guarded by the previous
  // `filteredSources` reference) rather than in an effect, so React re-renders
  // with the pruned selection before committing to the DOM — no extra painted
  // frame with a stale selection. `filteredSources` is memoized, so its
  // reference only changes when the visible set can actually change.
  const [prevFilteredSources, setPrevFilteredSources] =
    useState(filteredSources);
  if (filteredSources !== prevFilteredSources) {
    setPrevFilteredSources(filteredSources);
    const visibleUuids = new Set(filteredSources.map((s) => s.uuid));
    setSelectedSources((prev) => {
      const next = new Set([...prev].filter((uuid) => visibleUuids.has(uuid)));
      return next.size !== prev.size ? next : prev;
    });
  }

  // Drop sources from the selection once a delete completes. Pruning above only
  // clears sources that leave the store, so it misses "delete conversation"
  // (truncate), where the source stays visible; this covers that case. Guarded
  // by the previous reference so it runs once per completed deletion.
  const lastDeletedSources = useAppSelector(selectLastDeletedSources);
  const [prevLastDeletedSources, setPrevLastDeletedSources] =
    useState(lastDeletedSources);
  if (lastDeletedSources !== prevLastDeletedSources) {
    setPrevLastDeletedSources(lastDeletedSources);
    if (lastDeletedSources.length > 0) {
      setSelectedSources((prev) => {
        const next = new Set(prev);
        for (const uuid of lastDeletedSources) {
          next.delete(uuid);
        }
        return next.size !== prev.size ? next : prev;
      });
    }
  }

  // Helper to get all source option elements in the list
  const getSourceOptions = useCallback((): HTMLElement[] => {
    const container = listRef.current?.element;
    if (!container) {
      return [];
    }
    return Array.from(
      container.querySelectorAll<HTMLElement>('[role="option"]'),
    );
  }, [listRef]);

  // Move focus to the previous source row
  const handleSourceUp = useCallback(() => {
    const options = getSourceOptions();
    if (options.length === 0) {
      return;
    }
    const currentIndex = options.findIndex(
      (el) =>
        el === document.activeElement || el.contains(document.activeElement),
    );
    const nextIndex = currentIndex <= 0 ? options.length - 1 : currentIndex - 1;
    options[nextIndex].focus();
  }, [getSourceOptions]);

  // Move focus to the next source row
  const handleSourceDown = useCallback(() => {
    const options = getSourceOptions();
    if (options.length === 0) {
      return;
    }
    const currentIndex = options.findIndex(
      (el) =>
        el === document.activeElement || el.contains(document.activeElement),
    );
    const nextIndex = currentIndex >= options.length - 1 ? 0 : currentIndex + 1;
    options[nextIndex].focus();
  }, [getSourceOptions]);

  useSidebarShortcuts({
    onSourceUp: handleSourceUp,
    onSourceDown: handleSourceDown,
    onSourceSelect: useCallback(() => {
      // Enter/Space on focused source is handled by Source.tsx's onKeyDown
    }, []),
    onDeleteCheckedSources: useCallback(() => {
      void handleBulkDelete();
    }, [handleBulkDelete]),
    enabled: focusedPanel === "sidebar",
  });

  return (
    <div className="flex-1 flex flex-col min-h-0">
      {/* Toolbar with controls and actions */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b flex-shrink-0">
        <Toolbar
          allSelected={allSelected}
          selectedCount={selectedSources.size}
          totalCount={filteredSources.length}
          onSelectAll={handleSelectAll}
          onBulkDelete={handleBulkDelete}
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
      <div className="flex-1 min-h-0 flex flex-col">
        <List
          listRef={listRef}
          role="listbox"
          rowCount={filteredSources.length}
          rowHeight={72}
          rowComponent={SourceRow}
          rowProps={{
            filteredSources,
            selectedSources,
            activeSourceUuid,
            onSelect: handleSourceSelect,
            onToggleStar: handleToggleStar,
          }}
          className="select-none"
        />
      </div>

      {/* Source counts */}
      <Counts
        totalCount={totalSourceCount}
        visibleCount={filteredSources.length}
        selectedCount={selectedSources.size}
        isFiltered={filter !== "all" || searchResults !== null}
      />
    </div>
  );
}

export default SourceList;
