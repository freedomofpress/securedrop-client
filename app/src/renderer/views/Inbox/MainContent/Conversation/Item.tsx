import {
  ItemUpdateType,
  type Item,
  type ItemUpdate,
} from "../../../../../types";
import "./Item.css";
import Message from "./Item/Message";
import Reply from "./Item/Reply";
import File from "./Item/File";
import { useAppDispatch, useAppSelector } from "../../../../hooks";
import {
  updateItem,
  updateItemFetchStatus,
} from "../../../../features/conversation/conversationSlice";

import { useEffect, useCallback } from "react";

interface ItemProps {
  item: Item;
  designation: string;
}

function Item({ item, designation }: ItemProps) {
  const dispatch = useAppDispatch();
  const session = useAppSelector((state) => state.session);

  useEffect(() => {
    window.electronAPI.onItemUpdate((item: Item) => {
      dispatch(updateItem(item));
    });
  }, [dispatch]);

  const onFetchStatusUpdate = useCallback(
    async (update: ItemUpdate) => {
      if (update.type === ItemUpdateType.FetchStatus) {
        dispatch(
          updateItemFetchStatus({
            sourceUuid: item.data.source ?? "",
            itemUuid: update.item_uuid,
            fetchStatus: update.fetch_status!,
            authToken: session.authData?.token,
          }),
        );
      }
    },
    [dispatch, item.data.source, session.authData?.token],
  );

  const kind = item.data.kind;
  if (kind === "message") {
    return <Message item={item} designation={designation} />;
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
    return <Reply item={item} />;
  }
  // Fallback
  return null;
}

export default Item;
