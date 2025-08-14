import type { Item } from "../../../../../../types";
import { useTranslation } from "react-i18next";
import "../Item.css";

interface ReplyProps {
  item: Item;
}

function Reply({ item }: ReplyProps) {
  const { t } = useTranslation("MainContent");
  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  return (
    <div
      className="flex items-start mb-4 justify-end"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center justify-start mb-1">
          <span className="author reply-author">You</span>
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
