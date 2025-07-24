import { useState, useEffect } from "react";
import { Checkbox, Button, Dropdown } from "antd";
import {
  StarFilled,
  StarOutlined,
  DeleteOutlined,
  MailOutlined,
  SortAscendingOutlined,
  SortDescendingOutlined,
  DownOutlined,
} from "@ant-design/icons";

import type { Source } from "../../../../types";
import { formatLastUpdated, getInitials, toTitleCase } from "../../../utils";

function Sources() {
  const [sources, setSources] = useState<Source[]>([]);
  const [selectedSources, setSelectedSources] = useState<Set<string>>(
    new Set(),
  );
  const [allSelected, setAllSelected] = useState(false);
  const [activeSourceId, setActiveSourceId] = useState<string | null>(null);
  const [sortedAsc, setSortedAsc] = useState(false);
  const [filter, setFilter] = useState<"all" | "unread">("all");

  useEffect(() => {
    const fetchSources = async () => {
      const sources = await window.electronAPI.getSources();
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

  // Handle source click to select as active
  const handleSourceClick = (sourceId: string) => {
    if (activeSourceId === sourceId) {
      // If already active, deselect it
      setActiveSourceId(null);
      return;
    }
    // Set the clicked source as active
    setActiveSourceId(sourceId);
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

  const handleFilterChange = (newFilter: "all" | "unread") => {
    setFilter(newFilter);
  };

  // Filter and sort sources based on the selected filter and sort order
  const filteredSources = sources
    .filter((source) => {
      if (filter === "unread") {
        return !source.isRead;
      }
      return true; // "all" filter shows everything
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
      key: "unread",
      label: "Unread",
      onClick: () => handleFilterChange("unread"),
    },
  ];

  return (
    <div className="flex-1 flex flex-col">
      {/* Header with select all and action buttons */}
      <div className="sd-bg-primary sd-border-secondary px-4 py-3 border-b">
        <div className="flex items-center justify-between">
          <div>
            {/* Select all checkbox */}
            <Checkbox
              checked={allSelected}
              indeterminate={
                selectedSources.size > 0 &&
                selectedSources.size < sources.length
              }
              onChange={(e) => handleSelectAll(e.target.checked)}
            />

            {/* Only display action buttons if sources are selected */}
            {selectedSources.size > 0 && (
              <>
                <Button
                  type="text"
                  icon={<DeleteOutlined />}
                  onClick={handleBulkDelete}
                />
                <Button
                  type="text"
                  icon={<MailOutlined />}
                  onClick={handleBulkToggleRead}
                />
              </>
            )}
          </div>

          <div>
            <Dropdown menu={{ items: dropdownItems }} trigger={["click"]}>
              <Button type="text">
                {filter === "all" ? "All" : "Unread"} <DownOutlined />
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
            />
          </div>
        </div>
      </div>

      {/* Sources list */}
      <div className="flex-1 overflow-y-auto">
        {filteredSources.map((source) => {
          const isSelected = selectedSources.has(source.uuid);
          const isActive = activeSourceId === source.uuid;
          const designation = toTitleCase(source.data.journalistDesignation);
          const initials = getInitials(designation);
          const lastUpdated = formatLastUpdated(source.data.lastUpdated);

          return (
            <div
              key={source.uuid}
              className={`flex items-center px-4 py-3 border-b border-gray-100 cursor-pointer transition-colors duration-150 ease-in-out hover:bg-gray-50
                ${isActive ? "bg-blue-50 border-l-4 border-l-blue-500" : ""}
                ${isSelected ? "bg-blue-25" : ""}
`}
              onClick={() => handleSourceClick(source.uuid)}
            >
              {/* Checkbox */}
              <Checkbox
                checked={isSelected}
                onChange={(e) => {
                  e.stopPropagation();
                  handleSourceSelect(source.uuid, e.target.checked);
                }}
                onClick={(e) => e.stopPropagation()}
              />

              {/* Star button */}
              <Button
                type="text"
                size="large"
                icon={
                  source.data.isStarred ? (
                    <StarFilled style={{ color: "#eab308" }} />
                  ) : (
                    <StarOutlined
                      className="text-gray-400"
                      style={{ color: "#9ca3af" }}
                    />
                  )
                }
                onClick={(e) => {
                  e.stopPropagation();
                  handleToggleStar(source.uuid, source.data.isStarred);
                }}
              />

              {/* Avatar with initials */}
              <div className="w-10 h-10 rounded-full bg-gray-100 border border-gray-300 flex items-center justify-center text-gray-600 font-medium text-sm flex-shrink-0">
                {initials}
              </div>

              {/* Source info */}
              <div className="flex-1 min-w-0 py-2 pl-3">
                <div className="flex items-center justify-between">
                  <div className="flex items-center gap-2 min-w-0">
                    <h3
                      className={`text-sm truncate ${
                        isActive ? "text-blue-700" : "text-gray-900"
                      } ${!source.isRead ? "font-bold" : "font-medium"}`}
                    >
                      {designation}
                    </h3>
                  </div>

                  {/* Date */}
                  <span
                    className={`text-xs text-gray-500 flex-shrink-0 ${
                      !source.isRead ? "font-bold" : "font-normal"
                    }`}
                  >
                    {lastUpdated}
                  </span>
                </div>
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
}

export default Sources;
