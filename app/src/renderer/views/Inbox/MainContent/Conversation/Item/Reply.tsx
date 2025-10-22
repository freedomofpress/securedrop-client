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
import { ClockCircleOutlined } from "@ant-design/icons";
import "../Item.css";
import "./Reply.css";

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

  // Get the journalist by ID (only for non-pending replies)
  const journalist = useAppSelector((state) =>
    !isPendingReply
      ? getJournalistById(state, replyData.journalist_uuid)
      : undefined,
  );

  // Get the current journalist (for pending replies)
  const currentJournalist = useAppSelector((state) =>
    sessionState.status === SessionStatus.Auth && sessionState.authData
      ? getJournalistById(state, sessionState.authData.journalistUUID)
      : undefined,
  );

  // Determine what to display for the author
  const getAuthorDisplay = () => {
    // Handle pending replies (journalist_uuid is empty)
    if (isPendingReply) {
      if (sessionState.status === SessionStatus.Auth && sessionState.authData) {
        // Online/authenticated mode: show current user's name
        if (currentJournalist) {
          return formatJournalistName(currentJournalist.data);
        }
        // Fallback to authData if journalist not yet in store
        const firstName = sessionState.authData.journalistFirstName;
        const lastName = sessionState.authData.journalistLastName;
        if (firstName || lastName) {
          return [firstName, lastName].filter(Boolean).join(" ");
        }
        return t("you");
      } else if (sessionState.status === SessionStatus.Offline) {
        // Offline mode: show "You"
        return t("you");
      }
      // Fallback (shouldn't happen - can't create replies when unauthenticated)
      return t("unknown");
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

  return (
    <div
      className="flex items-start mb-4 justify-end"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center justify-start mb-1 gap-1">
          <span className="author reply-author">{getAuthorDisplay()}</span>
          {isPendingReply && (
            <Tooltip title={t("pendingReplyTooltip")}>
              <ClockCircleOutlined
                data-testid="pending-reply-icon"
                className="pending-reply-icon"
              />
            </Tooltip>
          )}
        </div>
        <div className="reply-box whitespace-pre-wrap">
          {isEncrypted ? (
            <span className="italic text-gray-500">{t("itemEncrypted")}</span>
          ) : (
            messageContent
          )}
        </div>
      </div>
    </div>
  );
}

export default Reply;
