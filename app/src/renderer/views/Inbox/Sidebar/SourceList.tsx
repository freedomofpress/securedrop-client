import { useState, useEffect, useMemo, useCallback } from "react";
import { useParams, useNavigate } from "react-router";
import { List, useListRef } from "react-window";
import { useTranslation } from "react-i18next";
import { Modal, Button } from "antd";

import type { RowComponentProps } from "react-window";
import Source from "./SourceList/Source";
import { useDebounce, useAppDispatch, useAppSelector } from "../../../hooks";
import {
  fetchSources,
  selectSources,
} from "../../../features/sources/sourcesSlice";
import { fetchConversation } from "../../../features/conversation/conversationSlice";
import Toolbar, { type filterOption } from "./SourceList/Toolbar";
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
  const navigate = useNavigate();
  const { t } = useTranslation("Sidebar");
  const listRef = useListRef(null);

  const sources = useAppSelector(selectSources);
  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [allSelected, setAllSelected] = useState(false);
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<filterOption>("all");
  const [searchTerm, setSearchTerm] = useState("");
  const [dropdownOpen, setDropdownOpen] = useState(false);
  const [deleteModalOpen, setDeleteModalOpen] = useState(false);
  const [deleteModalLoading, setDeleteModalLoading] = useState(false);
  // Sources targeted for deletion
  const [pendingDeleteSources, setPendingDeleteSources] = useState<Set<string>>(
    new Set(),
  );
  const [deleteCounts, setDeleteCounts] = useState<{
    messages: number;
    files: number;
    replies: number;
  }>({ messages: 0, files: 0, replies: 0 });

  // Debounce search term to avoid excessive filtering
  const debouncedSearchTerm = useDebounce(searchTerm, 300);
  const [searchResults, setSearchResults] = useState<SearchResult[] | null>(
    null,
  );

  useEffect(() => {
    dispatch(fetchSources());
  }, [dispatch]);

  // Perform search via IPC when search term changes or sources update
  useEffect(() => {
    let cancelled = false;

    if (!debouncedSearchTerm.trim()) {
      setSearchResults(null);
      return;
    }

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
  }, [debouncedSearchTerm, sources]);

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

  // Opens the delete confirmation modal for the given set of sources.
  const openDeleteModal = useCallback(async (sources: Set<string>) => {
    if (sources.size === 0) {
      return;
    }

    setPendingDeleteSources(sources);
    setDeleteModalOpen(true);
    setDeleteModalLoading(true);

    try {
      // Fetch all source items to count messages, files, and replies
      let totalMessages = 0;
      let totalFiles = 0;
      let totalReplies = 0;

      for (const sourceUuid of sources) {
        const sourceWithItems =
          await window.electronAPI.getSourceWithItems(sourceUuid);
        if (sourceWithItems) {
          // Count messages, files, and replies
          for (const item of sourceWithItems.items) {
            if (item.data.kind === "message") {
              totalMessages++;
            } else if (item.data.kind === "file") {
              totalFiles++;
            } else if (item.data.kind === "reply") {
              totalReplies++;
            }
          }
        }
      }

      setDeleteCounts({
        messages: totalMessages,
        files: totalFiles,
        replies: totalReplies,
      });
    } catch (error) {
      console.error("Error fetching source items:", error);
      setDeleteCounts({ messages: 0, files: 0, replies: 0 });
    } finally {
      setDeleteModalLoading(false);
    }
  }, []);

  // Bulk delete button: opens modal for the currently checked sources
  const handleBulkDelete = useCallback(async () => {
    await openDeleteModal(new Set(selectedSources));
  }, [selectedSources, openDeleteModal]);

  // Keyboard shortcut: Ctrl+Delete deletes the current source
  useShortcut(
    "deleteSource",
    () => {
      if (!deleteModalOpen && activeSourceUuid) {
        void openDeleteModal(new Set([activeSourceUuid]));
      }
    },
    undefined,
    [openDeleteModal, deleteModalOpen, activeSourceUuid],
  );

  const handleDeleteModalCancel = useCallback(() => {
    setPendingDeleteSources(new Set());
    setDeleteModalOpen(false);
  }, []);

  const handleDeleteAction = useCallback(
    async (eventType: PendingEventType) => {
      try {
        for (const sourceUuid of pendingDeleteSources) {
          const sourceToDelete = sources.find((x) => x.uuid === sourceUuid);
          await window.electronAPI.addPendingSourceEvent(
            sourceUuid,
            eventType,
            eventType === PendingEventType.SourceConversationTruncated
              ? {
                  upper_bound: sourceToDelete?.lastInteractionCount ?? 0,
                }
              : undefined,
          );
        }
        // If we deleted an account and it was the currently active source, navigate away
        if (
          eventType === PendingEventType.SourceDeleted &&
          activeSourceUuid &&
          pendingDeleteSources.has(activeSourceUuid)
        ) {
          navigate("/");
        }
        // If we deleted a conversation and there's an active source, refresh the conversation
        if (
          eventType === PendingEventType.SourceConversationTruncated &&
          activeSourceUuid
        ) {
          dispatch(fetchConversation(activeSourceUuid));
        }
        // Update local state immediately with projected changes
        dispatch(fetchSources());
        // Remove the deleted sources from the checkbox selection if they were checked
        setSelectedSources((prev) => {
          const next = new Set(prev);
          for (const uuid of pendingDeleteSources) {
            next.delete(uuid);
          }
          if (next.size === 0) {
            setAllSelected(false);
          }
          return next;
        });
        setPendingDeleteSources(new Set());
        setDeleteModalOpen(false);
      } catch (error) {
        console.error("Failed to delete source(s):", error);
      }
    },
    [pendingDeleteSources, dispatch, activeSourceUuid, navigate, sources],
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
      const sourcesByUuid = new Map(sources.map((s) => [s.uuid, s]));
      const seen = new Set<string>();

      for (const sr of searchResults) {
        if (seen.has(sr.sourceUuid)) {
          continue;
        }
        seen.add(sr.sourceUuid);
        const source = sourcesByUuid.get(sr.sourceUuid);
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
      searchedSources = sources;
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

  // Handle select all checkbox
  const handleSelectAll = useCallback(
    (checked: boolean) => {
      if (checked) {
        setSelectedSources(new Set(filteredSources.map((source) => source.uuid)));
        setAllSelected(true);
      } else {
        setSelectedSources(new Set());
        setAllSelected(false);
      }
    },
    [filteredSources],
  );

  // When the visible sources change (due to filter or search), trim the selection
  // to only sources that are still visible.
  useEffect(() => {
    const visibleUuids = new Set(filteredSources.map((s) => s.uuid));
    setSelectedSources((prev) => {
      const next = new Set([...prev].filter((uuid) => visibleUuids.has(uuid)));
      if (next.size !== prev.size) {
        setAllSelected(next.size > 0 && next.size === filteredSources.length);
        return next;
      }
      return prev;
    });
  }, [filteredSources]);

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
          totalCount={sources.length}
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

      {/* Delete confirmation modal */}
      <Modal
        open={deleteModalOpen}
        data-testid="delete-modal"
        closable={false}
        title={
          <span data-testid="delete-modal-title">
            {pendingDeleteSources.size === 1
              ? t("sourcelist.deleteDialog.single.message")
              : t("sourcelist.deleteDialog.multiple.message", {
                  count: pendingDeleteSources.size,
                })}
          </span>
        }
        getContainer={() => document.getElementById("root") || document.body}
        onCancel={handleDeleteModalCancel}
        footer={[
          <Button
            key="cancel"
            data-testid="delete-modal-cancel-button"
            onClick={handleDeleteModalCancel}
            autoFocus
          >
            {t("sourcelist.deleteDialog.cancelButton")}
          </Button>,
          <Button
            key="deleteConversation"
            data-testid="delete-modal-delete-conversation-button"
            type="primary"
            onClick={() =>
              handleDeleteAction(PendingEventType.SourceConversationTruncated)
            }
          >
            {pendingDeleteSources.size === 1
              ? t("sourcelist.deleteDialog.single.keepAccountButton")
              : t("sourcelist.deleteDialog.multiple.keepAccountsButton")}
          </Button>,
          <Button
            key="deleteAccount"
            data-testid="delete-modal-delete-account-button"
            type="primary"
            danger
            onClick={() => handleDeleteAction(PendingEventType.SourceDeleted)}
          >
            {pendingDeleteSources.size === 1
              ? t("sourcelist.deleteDialog.single.deleteAccountButton")
              : t("sourcelist.deleteDialog.multiple.deleteAccountsButton")}
          </Button>,
        ]}
      >
        <div data-testid="delete-modal-content">
          <p>{t("sourcelist.deleteDialog.warning")}</p>
          {deleteModalLoading ? (
            <p className="text-gray-600 italic">
              {t("sourcelist.deleteDialog.countingItems")}
            </p>
          ) : (
            <>
              {(deleteCounts.messages > 0 ||
                deleteCounts.files > 0 ||
                deleteCounts.replies > 0) && (
                <div className="mt-3">
                  <p className="font-medium text-gray-800">
                    {t("sourcelist.deleteDialog.itemCountsHeader")}
                  </p>
                  <ul className="mt-1 ml-4 list-none text-gray-700">
                    {deleteCounts.messages > 0 && (
                      <li>
                        {t("sourcelist.deleteDialog.messageCount", {
                          count: deleteCounts.messages,
                        })}
                      </li>
                    )}
                    {deleteCounts.files > 0 && (
                      <li>
                        {t("sourcelist.deleteDialog.fileCount", {
                          count: deleteCounts.files,
                        })}
                      </li>
                    )}
                    {deleteCounts.replies > 0 && (
                      <li>
                        {t("sourcelist.deleteDialog.replyCount", {
                          count: deleteCounts.replies,
                        })}
                      </li>
                    )}
                  </ul>
                </div>
              )}
            </>
          )}
        </div>
      </Modal>
    </div>
  );
}

export default SourceList;
