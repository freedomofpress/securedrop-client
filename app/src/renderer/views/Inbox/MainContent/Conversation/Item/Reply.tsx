import type { Item, ReplyMetadata } from "../../../../../../types";
import { useTranslation } from "react-i18next";
import {
  getSessionState,
  SessionStatus,
} from "../../../../../features/session/sessionSlice";
import { getJournalistById } from "../../../../../features/journalists/journalistsSlice";
import { formatJournalistName } from "../../../../../utils";
import { useAppSelector } from "../../../../../hooks";
import { Tooltip } from "antd";
import { Clock, Check, CheckCheck } from "lucide-react";
import TruncatedText from "../../../../../components/TruncatedText";
import "../Item.css";
import "./Reply.css";

// Reply sync states
type ReplySyncState = "pending" | "sent" | "seen";

interface ReplyProps {
  item: Item;
}

function Reply({ item }: ReplyProps) {
  const { t } = useTranslation("MainContent");
  const sessionState = useAppSelector(getSessionState);

  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  // Cast item.data to ReplyMetadata since we know this is a reply
  const replyData = item.data as ReplyMetadata;

  // Derive the sync state
  const syncState: ReplySyncState =
    replyData.journalist_uuid === ""
      ? "pending"
      : replyData.is_deleted_by_source
        ? "seen"
        : "sent";

  // Get the journalist by ID (only for non-pending replies)
  const journalist = useAppSelector((state) =>
    syncState !== "pending"
      ? getJournalistById(state, replyData.journalist_uuid)
      : undefined,
  );

  // Determine what to display for the author
  const getAuthorDisplay = () => {
    // Handle pending replies (journalist_uuid is empty)
    if (syncState === "pending") {
      return t("you");
    }

    // Handle normal replies (with journalist_uuid)
    if (sessionState.status !== SessionStatus.Auth || !sessionState.authData) {
      // Not authenticated - show journalist name or "Unknown"
      return journalist ? formatJournalistName(journalist.data) : t("unknown");
    }

    // Authenticated - check if current user is the author
    const currentUserUUID = sessionState.authData.journalistUUID;
    if (currentUserUUID === replyData.journalist_uuid) {
      return t("you");
    }

    // Different journalist, show their name
    return journalist ? formatJournalistName(journalist.data) : t("unknown");
  };

  // Get the status icon and tooltip text based on sync state
  const statusIcon = (() => {
    switch (syncState) {
      case "pending":
        return {
          tooltip: t("pendingReplyTooltip"),
          icon: (
            <Clock
              data-testid="pending-reply-icon"
              className="reply-status-icon pending-reply-icon"
              size={14}
            />
          ),
        };
      case "sent":
        return {
          tooltip: t("successReplyTooltip"),
          icon: (
            <Check
              data-testid="sent-reply-icon"
              className="reply-status-icon sent-reply-icon"
              size={14}
            />
          ),
        };
      case "seen":
        return {
          tooltip: t("seenReplyTooltip"),
          icon: (
            <CheckCheck
              data-testid="seen-reply-icon"
              className="reply-status-icon seen-reply-icon"
              size={14}
            />
          ),
        };
    }
  })();

  return (
    <div
      className="flex items-start mb-4 justify-end"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center justify-start mb-1 gap-1">
          <span className="author reply-author">{getAuthorDisplay()}</span>
        </div>
        <Tooltip title={statusIcon.tooltip} placement="bottomRight">
          <div className="reply-box whitespace-pre-wrap overflow-hidden relative with-status-icon">
            {isEncrypted ? (
              <span className="italic text-gray-500">{t("itemEncrypted")}</span>
            ) : (
              <TruncatedText text={messageContent} />
            )}
            {statusIcon.icon}
          </div>
        </Tooltip>
      </div>
    </div>
  );
}

export default Reply;
