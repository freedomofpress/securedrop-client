import type { Item, ReplyMetadata } from "../../../../../../types";
import { useTranslation } from "react-i18next";
import { useState, useEffect, useRef } from "react";
import {
  getSessionState,
  SessionStatus,
} from "../../../../../features/session/sessionSlice";
import { getJournalistById } from "../../../../../features/journalists/journalistsSlice";
import { formatJournalistName } from "../../../../../utils";
import { useAppSelector } from "../../../../../hooks";
import { Tooltip } from "antd";
import { ClockCircleOutlined, CheckCircleOutlined } from "@ant-design/icons";
import TruncatedText from "../../../../../components/TruncatedText";
import "../Item.css";
import "./Reply.css";

// Reply sync states
type ReplySyncState = "pending" | "success" | "synced";

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

  // Check if this is a pending reply (journalist_uuid is empty until server processes it)
  const isPendingReply = replyData.journalist_uuid === "";

  // Track whether we should show the success animation
  // This is set when a reply transitions from pending to synced
  const [showSuccessAnimation, setShowSuccessAnimation] = useState(false);
  const prevIsPendingRef = useRef(isPendingReply);

  // Detect transition from pending to synced and trigger success animation
  useEffect(() => {
    // Only trigger if transitioning from pending to synced
    if (prevIsPendingRef.current && !isPendingReply) {
      // Use queueMicrotask to avoid synchronous setState within effect
      queueMicrotask(() => setShowSuccessAnimation(true));

      // Clear the success animation after 3 seconds
      // NOTE: Keep this duration in sync with the CSS animation in Reply.css
      const timer = setTimeout(() => {
        setShowSuccessAnimation(false);
      }, 3000);

      prevIsPendingRef.current = isPendingReply;
      return () => clearTimeout(timer);
    }

    prevIsPendingRef.current = isPendingReply;
    return undefined;
  }, [isPendingReply]);

  // Derive the sync state from the current state
  const syncState: ReplySyncState = isPendingReply
    ? "pending"
    : showSuccessAnimation
      ? "success"
      : "synced";

  // Get the journalist by ID (only for non-pending replies)
  const journalist = useAppSelector((state) =>
    !isPendingReply
      ? getJournalistById(state, replyData.journalist_uuid)
      : undefined,
  );

  // Determine what to display for the author
  const getAuthorDisplay = () => {
    // Handle pending replies (journalist_uuid is empty)
    if (isPendingReply) {
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

  // Determine if we need extra padding for the status icon
  const showStatusIcon = syncState !== "synced";

  // Render the appropriate status icon based on sync state
  const renderStatusIcon = () => {
    if (syncState === "pending") {
      return (
        <Tooltip title={t("pendingReplyTooltip")}>
          <ClockCircleOutlined
            data-testid="pending-reply-icon"
            className="reply-status-icon pending-reply-icon"
          />
        </Tooltip>
      );
    }
    if (syncState === "success") {
      return (
        <Tooltip title={t("successReplyTooltip")}>
          <CheckCircleOutlined
            data-testid="success-reply-icon"
            className="reply-status-icon success-reply-icon"
          />
        </Tooltip>
      );
    }
    return null;
  };

  return (
    <div
      className="flex items-start mb-4 justify-end"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center justify-start mb-1 gap-1">
          <span className="author reply-author">{getAuthorDisplay()}</span>
        </div>
        <div
          className={`reply-box whitespace-pre-wrap relative ${showStatusIcon ? "with-status-icon" : ""}`}
        >
          {isEncrypted ? (
            <span className="italic text-gray-500">{t("itemEncrypted")}</span>
          ) : (
            <TruncatedText text={messageContent} />
          )}
          {renderStatusIcon()}
        </div>
      </div>
    </div>
  );
}

export default Reply;
