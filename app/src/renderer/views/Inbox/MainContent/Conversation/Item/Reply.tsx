import { useSelector } from "react-redux";
import type { Item, ReplyMetadata } from "../../../../../../types";
import { useTranslation } from "react-i18next";
import {
  getSessionState,
  SessionStatus,
} from "../../../../../features/session/sessionSlice";
import { getJournalists } from "../../../../../features/journalists/journalistsSlice";
import { formatJournalistName } from "../../../../../utils";
import "../Item.css";

interface ReplyProps {
  item: Item;
}

function Reply({ item }: ReplyProps) {
  const { t } = useTranslation("MainContent");
  const sessionState = useSelector(getSessionState);
  const journalists = useSelector(getJournalists);

  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  // Cast item.data to ReplyMetadata since we know this is a reply
  const replyData = item.data as ReplyMetadata;

  // Determine what to display for the author
  const getAuthorDisplay = () => {
    // If session is not Auth, always show author name
    if (sessionState.status !== SessionStatus.Auth || !sessionState.authData) {
      // Find the journalist by UUID
      const journalist = journalists.find(
        (j) => j.data.uuid === replyData.journalist_uuid,
      );
      return journalist ? formatJournalistName(journalist.data) : t("unknown");
    }

    // If session is Auth, check if current user is the author
    const currentUserUUID = sessionState.authData.journalistUUID;
    if (currentUserUUID === replyData.journalist_uuid) {
      return t("you");
    }

    // Different journalist, show their name
    const journalist = journalists.find(
      (j) => j.data.uuid === replyData.journalist_uuid,
    );
    return journalist ? formatJournalistName(journalist.data) : t("unknown");
  };

  return (
    <div
      className="flex items-start mb-4 justify-end"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center justify-start mb-1">
          <span className="author reply-author">{getAuthorDisplay()}</span>
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
