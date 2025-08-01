import type { Item } from "../../../../../../types";
import { toTitleCase } from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import { useTranslation } from "react-i18next";
import "../Item.css";

interface MessageProps {
  item: Item;
  designation: string;
}

function Message({ item, designation }: MessageProps) {
  const { t } = useTranslation("MainContent");
  const titleCaseDesignation = toTitleCase(designation);
  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

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

export default Message;
