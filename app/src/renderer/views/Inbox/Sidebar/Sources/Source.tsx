import { Checkbox, Button } from "antd";
import { StarFilled, StarOutlined, PaperClipOutlined } from "@ant-design/icons";

import type { Source as SourceType } from "../../../../../types";
import { formatLastUpdated, getInitials, toTitleCase } from "../../../../utils";

interface SourceProps {
  source: SourceType;
  isSelected: boolean;
  isActive: boolean;
  onSelect: (sourceId: string, checked: boolean) => void;
  onToggleStar: (sourceId: string, currentlyStarred: boolean) => void;
  onClick: (sourceId: string) => void;
}

function Source({
  source,
  isSelected,
  isActive,
  onSelect,
  onToggleStar,
  onClick,
}: SourceProps) {
  const designation = toTitleCase(source.data.journalistDesignation);
  const initials = getInitials(designation);
  const lastUpdated = formatLastUpdated(source.data.lastUpdated);

  return (
    <div
      className={`flex items-center px-4 py-3 border-b border-gray-100 cursor-pointer transition-colors duration-150 ease-in-out hover:bg-gray-50
        ${isActive ? "bg-blue-50 border-l-4 border-l-blue-500" : ""}
        ${isSelected ? "bg-blue-25" : ""}
`}
      onClick={() => onClick(source.uuid)}
    >
      {/* Checkbox */}
      <Checkbox
        checked={isSelected}
        onChange={(e) => {
          e.stopPropagation();
          onSelect(source.uuid, e.target.checked);
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
          onToggleStar(source.uuid, source.data.isStarred);
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
            <div className="flex flex-col min-w-0">
              <h3
                className={`text-sm truncate ${
                  isActive ? "text-blue-700" : "text-gray-900"
                } ${!source.isRead ? "font-bold" : "font-medium"}`}
              >
                {designation}
              </h3>
              {source.showMessagePreview && (
                <p
                  className={`text-xs text-gray-500 truncate ${
                    !source.isRead ? "font-medium" : "font-normal"
                  } ${source.messagePreview === "" ? "italic" : ""}`}
                >
                  {source.messagePreview === ""
                    ? "encrypted..."
                    : source.messagePreview}
                </p>
              )}
            </div>
          </div>

          {/* Date and attachment info */}
          <div className="flex flex-col items-end gap-1 flex-shrink-0">
            <span
              className={`text-xs text-gray-500 ${
                !source.isRead ? "font-bold" : "font-normal"
              }`}
            >
              {lastUpdated}
            </span>
            {source.hasAttachment && (
              <PaperClipOutlined className="text-xs text-gray-400" />
            )}
          </div>
        </div>
      </div>
    </div>
  );
}

export default Source;
