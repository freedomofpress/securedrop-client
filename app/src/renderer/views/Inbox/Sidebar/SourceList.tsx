import { useState, useEffect, useMemo, useCallback, useRef } from "react";
import { useParams, useNavigate } from "react-router";
import { FixedSizeList as List } from "react-window";
import { useTranslation } from "react-i18next";
import { Modal, Button } from "antd";

import Source from "./SourceList/Source";
import { useDebounce, useAppDispatch, useAppSelector } from "../../../hooks";
import {
  fetchSources,
  selectSources,
} from "../../../features/sources/sourcesSlice";
import { fetchConversation } from "../../../features/conversation/conversationSlice";
import Toolbar, { type filterOption } from "./SourceList/Toolbar";
import { PendingEventType } from "../../../../types";

function SourceList() {
  const { sourceUuid: activeSourceUuid } = useParams<{ sourceUuid?: string }>();
  const dispatch = useAppDispatch();
  const navigate = useNavigate();
  const { t } = useTranslation("Sidebar");

  const sources = useAppSelector(selectSources);
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
  const [deleteModalOpen, setDeleteModalOpen] = useState(false);
  const [deleteModalLoading, setDeleteModalLoading] = useState(false);
  const [deleteCounts, setDeleteCounts] = useState<{
    messages: number;
    files: number;
    replies: number;
  }>({ messages: 0, files: 0, replies: 0 });

  // Debounce search term to avoid excessive filtering
  const debouncedSearchTerm = useDebounce(searchTerm, 300);

  useEffect(() => {
    dispatch(fetchSources());
  }, [dispatch]);

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
      // Add pending event
      const eventType = currentlyStarred
        ? PendingEventType.Unstarred
        : PendingEventType.Starred;
      await window.electronAPI.addPendingSourceEvent(sourceId, eventType);

      // Update local state immediately with projected changes
      dispatch(fetchSources());
    },
    [dispatch],
  );

  const handleBulkDelete = useCallback(async () => {
    if (selectedSources.size === 0) {
      return;
    }

    setDeleteModalOpen(true);
    setDeleteModalLoading(true);

    try {
      // Fetch all source items to count messages, files, and replies
      let totalMessages = 0;
      let totalFiles = 0;
      let totalReplies = 0;

      for (const sourceUuid of selectedSources) {
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
  }, [selectedSources]);

  const handleDeleteModalCancel = useCallback(() => {
    setDeleteModalOpen(false);
  }, []);

  const handleDeleteAction = useCallback(
    async (eventType: PendingEventType) => {
      for (const sourceUuid of selectedSources) {
        await window.electronAPI.addPendingSourceEvent(sourceUuid, eventType);
      }
      // If we deleted an account and it was the currently active source, navigate away
      if (
        eventType === PendingEventType.SourceDeleted &&
        activeSourceUuid &&
        selectedSources.has(activeSourceUuid)
      ) {
        navigate("/");
      }
      // If we deleted a conversation and there's an active source, refresh the conversation
      if (
        eventType === PendingEventType.SourceConversationDeleted &&
        activeSourceUuid
      ) {
        dispatch(fetchConversation(activeSourceUuid));
      }
      // Update local state immediately with projected changes
      dispatch(fetchSources());
      // Uncheck all boxes
      setSelectedSources(new Set());
      setAllSelected(false);
      setDeleteModalOpen(false);
    },
    [selectedSources, dispatch, activeSourceUuid, navigate],
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

      {/* Delete confirmation modal */}
      <Modal
        open={deleteModalOpen}
        data-testid="delete-modal"
        closable={false}
        title={
          <span data-testid="delete-modal-title">
            {selectedSources.size === 1
              ? t("sourcelist.deleteDialog.single.message")
              : t("sourcelist.deleteDialog.multiple.message", {
                  count: selectedSources.size,
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
              handleDeleteAction(PendingEventType.SourceConversationDeleted)
            }
          >
            {selectedSources.size === 1
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
            {selectedSources.size === 1
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
