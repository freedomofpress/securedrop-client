import type { Item } from "../../../../../types";
import "./Item.css";
import Message from "./Item/Message";
import Reply from "./Item/Reply";
import File from "./Item/File";

interface ItemProps {
  item: Item;
  designation: string;
}

function Item({ item, designation }: ItemProps) {
  const kind = item.data.kind;
  if (kind === "message") {
    return <Message item={item} designation={designation} />;
  }
  if (kind === "file") {
    return <File item={item} designation={designation} />;
  }
  if (kind === "reply") {
    return <Reply item={item} />;
  }
  // Fallback
  return null;
}

export default Item;
