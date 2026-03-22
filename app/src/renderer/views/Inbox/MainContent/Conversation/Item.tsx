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
  updateItemFetchStatus,
  deleteItem,
} from "../../../../features/conversation/conversationSlice";
import { useTranslation } from "react-i18next";
import { Trash } from "lucide-react";
import { Button, Tooltip } from "antd";

import { memo, useCallback, useMemo } from "react";

interface ItemProps {
  item: Item;
  designation: string;
}

const Item = memo(function ItemComponent({ item, designation }: ItemProps) {
  const dispatch = useAppDispatch();
  const session = useAppSelector((state) => state.session);
  const { t } = useTranslation("MainContent");

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

  const onDeleteItem = useCallback(async () => {
    dispatch(
      deleteItem({ sourceUuid: item.data.source ?? "", itemUuid: item.uuid }),
    );
  }, [dispatch, item.data.source, item.uuid]);

  const deleteButton = useMemo(
    () => (
      <Tooltip title={t("deleteItem")}>
        <Button
          type="text"
          size="small"
          danger
          icon={<Trash size={16} />}
          onClick={onDeleteItem}
        />
      </Tooltip>
    ),
    [t, onDeleteItem],
  );

  const deleteButtonLeft = useMemo(
    () => (
      <Tooltip title={t("deleteItem")} placement="left">
        <Button
          type="text"
          size="small"
          danger
          icon={<Trash size={16} />}
          onClick={onDeleteItem}
        />
      </Tooltip>
    ),
    [t, onDeleteItem],
  );

  const kind = item.data.kind;
  if (kind === "message") {
    return (
      <Message
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
        deleteButton={deleteButton}
      />
    );
  }
  if (kind === "file") {
    return (
      <File
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
        deleteButton={deleteButton}
      />
    );
  }
  if (kind === "reply") {
    return <Reply item={item} deleteButton={deleteButtonLeft} />;
  }
  // Fallback
  return null;
});

export default Item;
