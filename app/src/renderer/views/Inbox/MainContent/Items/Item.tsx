import type { Item } from "../../../../../types";
import { toTitleCase } from "../../../../utils";
import "./Item.css";

interface ItemProps {
  item: Item;
  designation: string;
}

function Item({ item, designation }: ItemProps) {
  const kind = item.data.kind;
  const isReply = kind === "reply";
  const isMessage = kind === "message";
  const isFile = kind === "file";

  const titleCaseDesignation = toTitleCase(designation);

  // Message/reply content
  let messageContent = "";
  if ((isMessage || isReply) && item.plaintext) {
    messageContent = item.plaintext;
  }
  let isEncrypted = false;
  if (!item.plaintext) {
    isEncrypted = true;
  }

  // File content
  let fileContent = "";
  if (isFile) {
    fileContent = item.filename ? `Attachment: ${item.filename}` : "Attachment";
  }

  // Layout classes
  const baseClass = "flex items-start mb-4";
  const leftClass = "justify-start";
  const rightClass = "justify-end";

  if (isMessage) {
    return (
      <div
        className={`${baseClass} ${leftClass}`}
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

  if (isFile) {
    return (
      <div
        className={`${baseClass} ${leftClass}`}
        data-testid={`item-${item.uuid}`}
      >
        <div>
          <div className="flex items-center mb-1">
            <span className="author">{titleCaseDesignation}</span>
          </div>
          <div className="bg-gray-50 border border-gray-200 rounded-lg px-4 py-2 text-gray-700 max-w-xl italic">
            {fileContent}
          </div>
        </div>
      </div>
    );
  }

  if (isReply) {
    return (
      <div
        className={`${baseClass} ${rightClass}`}
        data-testid={`item-${item.uuid}`}
      >
        <div>
          <div className="flex items-center justify-start mb-1">
            <span className="author">You</span>
          </div>
          <div className="reply-box">
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

  // Fallback
  return null;
}

export default Item;
