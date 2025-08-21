import { Checkbox, Button, Tooltip } from "antd";
import { Star, Paperclip } from "lucide-react";
import { useTranslation } from "react-i18next";
import { memo, useMemo } from "react";

import StarFilled from "./StarFilled";

import type { Source as SourceType } from "../../../../../types";
import { formatDate, toTitleCase } from "../../../../utils";
import Avatar from "../../../../components/Avatar";

export interface SourceProps {
  source: SourceType;
  isSelected: boolean;
  isActive: boolean;
  onSelect: (sourceId: string, checked: boolean) => void;
  onToggleStar: (sourceId: string, currentlyStarred: boolean) => void;
  onClick: (sourceId: string) => void;
}

const Source = memo(function Source({
  source,
  isSelected,
  isActive,
  onSelect,
  onToggleStar,
  onClick,
}: SourceProps) {
  const { t, i18n } = useTranslation("Sidebar");
  const { t: tCommon } = useTranslation("common");

  const designation = useMemo(
    () => toTitleCase(source.data.journalist_designation),
    [source.data.journalist_designation],
  );

  const lastUpdated = useMemo(
    () => formatDate(source.data.last_updated, i18n.language, tCommon),
    [source.data.last_updated, i18n.language, tCommon],
  );

  return (
    <div
      className={`flex items-center px-4 py-3 border-b border-gray-100 cursor-pointer transition-colors duration-150 ease-in-out
        ${isActive ? "bg-blue-500 text-white hover:bg-blue-600" : "hover:bg-gray-50"}
        ${isSelected && !isActive ? "bg-blue-25" : ""}
        sd-source
        ${source.data.is_starred ? "sd-source-starred" : "sd-source-unstarred"}
        ${source.isRead ? "sd-source-read" : "sd-source-unread"}
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
        className={
          isActive
            ? "text-white [&_.ant-checkbox-inner]:bg-white [&_.ant-checkbox-inner]:border-white [&_.ant-checkbox-checked_.ant-checkbox-inner]:bg-white [&_.ant-checkbox-checked_.ant-checkbox-inner]:border-white"
            : ""
        }
        data-testid="source-checkbox"
      />

      {/* Star button */}
      <Tooltip title={t("source.toggleStar")}>
        <Button
          type="text"
          size="large"
          icon={
            source.data.is_starred ? (
              <StarFilled color="#eab308" size={20} />
            ) : (
              <Star
                color="#9ca3af"
                size={20}
                className={isActive ? "text-white" : "text-gray-400"}
              />
            )
          }
          onClick={(e) => {
            e.stopPropagation();
            onToggleStar(source.uuid, source.data.is_starred);
          }}
        />
      </Tooltip>

      {/* Avatar with initials */}
      <Avatar designation={designation} isActive={isActive} />

      {/* Source info */}
      <div className="flex-1 min-w-0 py-2 pl-3">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-2 min-w-0">
            <div className="flex flex-col min-w-0">
              <h3
                className={`text-sm truncate ${
                  isActive ? "text-white" : "text-gray-900"
                } ${!source.isRead ? "font-bold" : "font-medium"}`}
                data-testid="source-designation"
              >
                {designation}
              </h3>
              {source.showMessagePreview && (
                <p
                  className={`text-xs truncate ${
                    isActive ? "text-white opacity-80" : "text-gray-500"
                  } ${
                    !source.isRead ? "font-medium" : "font-normal"
                  } ${source.messagePreview === "" ? "italic" : ""}`}
                  data-testid="message-preview"
                >
                  {source.messagePreview === ""
                    ? t("source.encrypted")
                    : source.messagePreview}
                </p>
              )}
            </div>
          </div>

          {/* Date and attachment info */}
          <div className="flex flex-col items-end gap-1 flex-shrink-0">
            <span
              className={`text-xs ${
                isActive ? "text-white opacity-80" : "text-gray-500"
              } ${!source.isRead ? "font-bold" : "font-normal"}`}
            >
              {lastUpdated}
            </span>
            {source.hasAttachment && (
              <Paperclip
                size={18}
                className={`text-xs ${
                  isActive ? "text-white opacity-80" : "text-gray-400"
                }`}
                data-testid="attachment-icon"
              />
            )}
          </div>
        </div>
      </div>
    </div>
  );
});

export default Source;
