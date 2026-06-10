import {
  ItemUpdateType,
  type Item,
  type ItemUpdate,
} from "../../../../../types";
import "./Item.css";
import Message from "./Item/Message";
import File from "./Item/File";
import { useAppDispatch } from "../../../../hooks";
import {
  updateItemFetchStatus,
  deleteItem,
} from "../../../../features/conversation/conversationSlice";

import { useTranslation } from "react-i18next";
import { Modal } from "antd";

import React, { memo, useCallback } from "react";

interface ItemProps {
  item: Item;
  designation: string;
  positionInConversation?: number;
  totalConversationItems?: number;
}

const Item = memo(function ItemComponent({
  item,
  designation,
  positionInConversation,
  totalConversationItems,
}: ItemProps) {
  const dispatch = useAppDispatch();
  const { t } = useTranslation("MainContent");
  const [modal, contextHolder] = Modal.useModal();

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

  const onDeleteItem = useCallback(() => {
    dispatch(
      deleteItem({ sourceUuid: item.data.source ?? "", itemUuid: item.uuid }),
    );
  }, [dispatch, item.data.source, item.uuid]);

  const onDeleteClick = useCallback(() => {
    modal.confirm({
      getContainer: () => document.getElementById("root") || document.body,
      title: t("deleteItemModal.title"),
      content: t("deleteItemModal.content"),
      okText: t("deleteItemModal.delete"),
      cancelText: t("deleteItemModal.cancel"),
      okButtonProps: { danger: true },
      icon: null,
      onOk: onDeleteItem,
    });
  }, [modal, t, onDeleteItem]);

  const kind = item.data.kind;
  let content: React.ReactNode = null;
  if (kind === "message") {
    content = (
      <Message
        kind="message"
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
        onDelete={onDeleteClick}
        positionInConversation={positionInConversation}
        totalConversationItems={totalConversationItems}
      />
    );
  } else if (kind === "file") {
    content = (
      <File
        item={item}
        designation={designation}
        onUpdate={onFetchStatusUpdate}
        onDelete={onDeleteClick}
        positionInConversation={positionInConversation}
        totalConversationItems={totalConversationItems}
      />
    );
  } else if (kind === "reply") {
    content = (
      <Message
        kind="reply"
        item={item}
        onDelete={onDeleteClick}
        positionInConversation={positionInConversation}
        totalConversationItems={totalConversationItems}
      />
    );
  }

  if (content === null) {
    return null;
  }

  return (
    <>
      {contextHolder}
      {content}
    </>
  );
});

export default Item;
