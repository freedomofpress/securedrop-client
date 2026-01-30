import { memo } from "react";
import {
  FetchStatus,
  ItemUpdateType,
  type Item,
  type ItemUpdate,
} from "../../../../../../types";
import { toTitleCase } from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import { useTranslation } from "react-i18next";
import { RotateCw } from "lucide-react";
import { Button, Tooltip, theme } from "antd";
import { ExclamationCircleTwoTone } from "@ant-design/icons";
import "../Item.css";

interface MessageProps {
  item: Item;
  designation: string;
  onUpdate: (update: ItemUpdate) => void;
}

const Message = memo(function Message({
  item,
  designation,
  onUpdate,
}: MessageProps) {
  const { t } = useTranslation("MainContent");
  const { token } = theme.useToken();
  const titleCaseDesignation = toTitleCase(designation);
  const isFailed = item.fetch_status === FetchStatus.FailedTerminal;
  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  const retryFetch = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  return (
    <div
      className="flex items-start mb-4 justify-start"
      data-testid={`item-${item.uuid}`}
    >
      <Avatar designation={titleCaseDesignation} isActive={false} />
      <div className="ml-3">
        <div className="flex items-center mb-1">
          <span className="author">{titleCaseDesignation}</span>
        </div>
        <div className="message-box whitespace-pre-wrap">
          {isFailed ? (
            <div className="flex items-center justify-between">
              <div className="flex items-center gap-2">
                <ExclamationCircleTwoTone
                  twoToneColor={token.colorError}
                  style={{ fontSize: 16 }}
                />
                <span className="italic text-gray-500">
                  {t("messageFailed")}
                </span>
              </div>
              <Tooltip title={t("retryFetch")}>
                <Button
                  type="text"
                  size="small"
                  icon={<RotateCw size={14} />}
                  onClick={retryFetch}
                />
              </Tooltip>
            </div>
          ) : isEncrypted ? (
            <span className="italic text-gray-500">{t("itemEncrypted")}</span>
          ) : (
            messageContent
          )}
        </div>
      </div>
    </div>
  );
});

export default Message;
