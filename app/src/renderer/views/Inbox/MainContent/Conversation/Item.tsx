import {
  ItemUpdateType,
  type Item,
  type ItemUpdate,
} from "../../../../../types";
import "./Item.css";
import Message from "./Item/Message";
import File from "./Item/File";
import { useAppDispatch } from "../../../../hooks";
import { updateItemFetchStatus } from "../../../../features/conversation/conversationSlice";

import { memo, useCallback } from "react";

interface ItemProps {
  item: Item;
  designation: string;
}

const Item = memo(function ItemComponent({ item, designation }: ItemProps) {
  const dispatch = useAppDispatch();

  const onFetchStatusUpdate = useCallback(
    async (update: ItemUpdate) => {
      if (update.type === ItemUpdateType.FetchStatus) {
        dispatch(
          updateItemFetchStatus({
            sourceUuid: item.data.source ?? "",
            itemUuid: update.item_uuid,
            fetchStatus: update.fetch_status!,
          }),
        );
      }
    },
    [dispatch, item.data.source],
  );

  const kind = item.data.kind;
  if (kind === "message") {
    return (
      <Message
        kind="message"
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
      />
    );
  }
  if (kind === "file") {
    return (
      <File
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
      />
    );
  }
  if (kind === "reply") {
    return <Message kind="reply" item={item} onUpdate={onFetchStatusUpdate} />;
  }
  // Fallback
  return null;
});

export default Item;
