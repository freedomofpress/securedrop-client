import type { Item } from "../../../../../../types";
import "../Item.css";

interface ReplyProps {
  item: Item;
}

function Reply({ item }: ReplyProps) {
  const isEncrypted = !item.plaintext;
  const messageContent = item.plaintext || "";

  return (
    <div
      className="flex items-start mb-4 justify-end"
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

export default Reply;
