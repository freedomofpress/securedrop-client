import type { Item } from "../../../../../../types";
import { toTitleCase } from "../../../../../utils";
import "../Item.css";

interface MessageProps {
  item: Item;
  designation: string;
}

function Message({ item, designation }: MessageProps) {
  const titleCaseDesignation = toTitleCase(designation);
  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  return (
    <div
      className="flex items-start mb-4 justify-start"
      data-testid={`item-${item.uuid}`}
    >
      <div>
        <div className="flex items-center mb-1">
          <span className="author">{titleCaseDesignation}</span>
        </div>
        <div className="message-box">
          {isEncrypted ? (
            <span className="italic text-gray-500">
              Message is encrypted...
            </span>
          ) : (
            messageContent
          )}
        </div>
      </div>
    </div>
  );
}

export default Message;
