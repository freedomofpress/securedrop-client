import { useState, useEffect } from "react";
import { useNavigate, useParams } from "react-router";
import { Checkbox, Button, Dropdown, Input } from "antd";
import {
  DeleteOutlined,
  MailOutlined,
  SortAscendingOutlined,
  SortDescendingOutlined,
  DownOutlined,
  SearchOutlined,
} from "@ant-design/icons";

import type { Source as SourceType } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Source from "./Sources/Source";

type filterOption = "all" | "read" | "unread" | "starred" | "unstarred";

function Sources() {
  const navigate = useNavigate();
  const { sourceUuid: activeSourceUuid } = useParams<{ sourceUuid?: string }>();

  const [sources, setSources] = useState<SourceType[]>([]);
  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [allSelected, setAllSelected] = useState(false);
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<filterOption>("all");
  const [searchTerm, setSearchTerm] = useState("");

  useEffect(() => {
    const fetchSources = async () => {
      const sources = await window.electronAPI.getSources();
      console.log("Fetched sources:", sources);
      setSources(sources);
    };
    fetchSources();
  }, []);

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
    console.log(
      `Toggle star for source ${sourceId}, currently starred: ${currentlyStarred}`,
    );

    // Update local state optimistically
    setSources(
      sources.map((source) =>
        source.uuid === sourceId
          ? {
              ...source,
              data: { ...source.data, isStarred: !currentlyStarred },
            }
          : source,
      ),
    );
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
  };

  const handleFilterChange = (newFilter: filterOption) => {
    setFilter(newFilter);
  };

  // Filter and sort sources based on the selected filter and sort order
  const filteredSources = sources
    .filter((source) => {
      // First filter by search term
      const designation = toTitleCase(source.data.journalistDesignation);
      const matchesSearch = designation
        .toLowerCase()
        .includes(searchTerm.toLowerCase());

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
          return source.data.isStarred;
        case "unstarred":
          return !source.data.isStarred;
        case "all":
        default:
          return true; // "all" filter shows everything
      }
    })
    .sort((a, b) => {
      const dateA = new Date(a.data.lastUpdated).getTime();
      const dateB = new Date(b.data.lastUpdated).getTime();

      if (sortedAsc) {
        return dateA - dateB; // Ascending: oldest first
      } else {
        return dateB - dateA; // Descending: newest first
      }
    });

  const dropdownItems = [
    {
      key: "all",
      label: "All",
      onClick: () => handleFilterChange("all"),
    },
    {
      key: "read",
      label: "Read",
      onClick: () => handleFilterChange("read"),
    },
    {
      key: "unread",
      label: "Unread",
      onClick: () => handleFilterChange("unread"),
    },
    {
      key: "starred",
      label: "Starred",
      onClick: () => handleFilterChange("starred"),
    },
    {
      key: "unstarred",
      label: "Unstarred",
      onClick: () => handleFilterChange("unstarred"),
    },
  ];

  return (
    <div className="flex-1 flex flex-col">
      {/* Header with select all and action buttons */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b">
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
                <Button
                  type="text"
                  icon={<DeleteOutlined />}
                  onClick={handleBulkDelete}
                  data-testid="bulk-delete-button"
                />
                <Button
                  type="text"
                  icon={<MailOutlined />}
                  onClick={handleBulkToggleRead}
                  data-testid="bulk-toggle-read-button"
                />
              </>
            )}
          </div>

          <Input
            placeholder="Search"
            prefix={<SearchOutlined />}
            value={searchTerm}
            onChange={(e) => setSearchTerm(e.target.value)}
            className="flex-1 min-w-0 max-w-xs"
            allowClear
          />

          <div className="flex items-center gap-1 flex-shrink-0">
            <Dropdown menu={{ items: dropdownItems }} trigger={["click"]}>
              <Button type="text" data-testid="filter-dropdown">
                {filter.charAt(0).toUpperCase() + filter.slice(1)}{" "}
                <DownOutlined />
              </Button>
            </Dropdown>

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
          </div>
        </div>
      </div>

      {/* Sources list */}
      <div className="flex-1 overflow-y-auto">
        {filteredSources.map((source) => {
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
      </div>
    </div>
  );
}

export default Sources;
