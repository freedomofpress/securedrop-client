import type { Item, SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Conversation/Item";
import NewMessagesDivider from "./Conversation/NewMessagesDivider";
import EmptyConversation from "./EmptyConversation";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import { memo, useMemo, useCallback, useState, useEffect } from "react";
import { useAppDispatch, useAppSelector, useDebounce } from "../../../hooks";
import { useStore } from "react-redux";
import { useShortcut } from "../../../shortcuts";
import { fetchSources } from "../../../features/sources/sourcesSlice";
import {
  setDraft,
  clearDraft,
  selectDraft,
} from "../../../features/drafts/draftsSlice";
import {
  fetchConversation,
  fetchOlderConversationItems,
  selectHasMoreHistoricalItems,
  selectOlderItemsLoading,
  selectItemIds,
  selectItemsById,
  updateItemFetchStatus,
} from "../../../features/conversation/conversationSlice";
import { syncMetadata } from "../../../features/sync/syncSlice";
import useConversationScroll from "./Conversation/useConversationScroll";
import "./Conversation.css";
import { FetchStatus } from "../../../../types";
import type { RootState } from "../../../store";
import { List } from "react-window";
import type { RowComponentProps } from "react-window";

const MAX_REPLY_LENGTH = 5000;

interface ConversationProps {
  sourceWithItems: Omit<SourceWithItems, "items"> | null;
}

type VirtualRow =
  | { kind: "item"; itemId: string }
  | { kind: "divider" };

interface ConversationRowProps {
  virtualRows: VirtualRow[];
  designation: string;
}

// Each row selects its own item from the store so only the specific row
// re-renders on per-item updates (download progress, IPC ticks).
// nosemgrep: react-component-missing-memo
function ConversationRow({
  index,
  style,
  virtualRows,
  designation,
}: RowComponentProps<ConversationRowProps>) {
  const row = virtualRows[index];
  const itemId = row.kind === "item" ? row.itemId : null;
  const item = useAppSelector((state: RootState) =>
    itemId ? state.conversation.itemsById[itemId] : undefined,
  );

  return (
    <div style={style} className="px-4">
      {row.kind === "divider" ? (
        <NewMessagesDivider />
      ) : item ? (
        <Item item={item} designation={designation} />
      ) : null}
    </div>
  );
}

const Conversation = memo(function Conversation({
  sourceWithItems,
}: ConversationProps) {
  const { t } = useTranslation("MainContent");
  const dispatch = useAppDispatch();
  const store = useStore<RootState>();
  const session = useAppSelector((state) => state.session);
  const hasMoreHistoricalItems = useAppSelector(selectHasMoreHistoricalItems);
  const olderItemsLoading = useAppSelector(selectOlderItemsLoading);
  const sourceUuid = sourceWithItems?.uuid ?? "";
  const savedDraft = useAppSelector(selectDraft(sourceUuid));
  const [form] = Form.useForm();
  const [messageValue, setMessageValue] = useState(savedDraft);
  const debouncedMessage = useDebounce(messageValue, 300);

  // Stable ordered item IDs — only changes when items are added or removed,
  // not on per-item updates like download progress ticks.
  const itemIds = useAppSelector(selectItemIds);

  // Snapshot of item data for the current itemIds; recomputed only when
  // itemIds changes (not on every itemsById tick).
  const items = useMemo((): Item[] => {
    const { itemsById } = store.getState().conversation;
    return itemIds
      .map((id) => itemsById[id])
      .filter((item): item is Item => item !== undefined);
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [itemIds, store]);

  const {
    acknowledgeNewMessages,
    dividerIndex,
    dividerItemUuid,
    dynamicRowHeight,
    hasItems,
    heightsReady,
    listRef,
    newItemIds,
    oldItemIds,
    scrollElement,
    showNewMessagesButton,
    scrollToBottom,
  } = useConversationScroll(sourceWithItems, items);

  // Restore draft when switching sources (including initial mount)
  useEffect(() => {
    setMessageValue(savedDraft);
    form.setFieldsValue({ message: savedDraft || undefined });
    // Only run when the source changes, not when savedDraft changes from our own typing
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [sourceUuid]);

  // Persist draft to Redux (debounced)
  useEffect(() => {
    if (sourceUuid) {
      dispatch(setDraft({ sourceUuid, content: debouncedMessage }));
    }
  }, [debouncedMessage, sourceUuid, dispatch]);

  const designation = useMemo(
    () => sourceWithItems?.data.journalist_designation,
    [sourceWithItems?.data.journalist_designation],
  );

  const placeholderText = useMemo(
    () =>
      t("conversation.messagePlaceholder", {
        designation: designation ? toTitleCase(designation) : "",
      }),
    [t, designation],
  );

  const isSendDisabled = useMemo(
    () =>
      !messageValue ||
      !messageValue.trim() ||
      messageValue.length > MAX_REPLY_LENGTH,
    [messageValue],
  );

  const handleSubmit = useCallback(
    async (values: { message: string }) => {
      if (!sourceWithItems || !values.message?.trim()) {
        return;
      }

      // Clear the form immediately for better UX
      form.resetFields();
      setMessageValue("");
      dispatch(clearDraft(sourceWithItems.uuid));

      // Read current item data at submit time rather than capturing stale closure.
      const { itemIds: currentIds, itemsById: currentById } =
        store.getState().conversation;
      const lastId = currentIds.at(-1);
      const lastItem = lastId ? currentById[lastId] : undefined;

      // Calculate the likely interactionCount this reply will be assigned; it
      // may not be correct (e.g. if the conversation was deleted) but it'll display
      // in the correct order while pending and then get adjusted on the server.
      const nextInteractionCount = (lastItem?.data.interaction_count || 0) + 1;

      try {
        await window.electronAPI.addPendingReplySentEvent(
          values.message,
          sourceWithItems.uuid,
          nextInteractionCount,
        );

        if (dividerItemUuid) {
          acknowledgeNewMessages();
        }

        // Update local state immediately with projected changes
        dispatch(fetchSources());
        dispatch(fetchConversation(sourceWithItems.uuid));

        // Trigger sync to send the pending reply to the server
        if (session.authData && import.meta.env.MODE !== "test") {
          dispatch(syncMetadata(session.authData));
        }
      } catch (error) {
        console.error("Failed to send reply:", error);
        // Restore the message on error
        form.setFieldsValue({ message: values.message });
        setMessageValue(values.message);
      }
    },
    [
      acknowledgeNewMessages,
      dispatch,
      dividerItemUuid,
      form,
      session.authData,
      sourceWithItems,
      store,
    ],
  );

  // Keyboard shortcut: Ctrl+Enter sends reply
  useShortcut("sendReply", () => form.submit(), undefined, [form]);

  // Keyboard shortcut: Ctrl+D initiates download for all files
  const downloadAllFiles = useCallback(() => {
    if (!sourceWithItems || !session.authData?.token) {
      return;
    }

    const token = session.authData.token;
    // Read current item data at call time.
    const { itemIds: currentIds, itemsById: currentById } =
      store.getState().conversation;
    currentIds.forEach((id) => {
      const item = currentById[id];
      if (
        item?.data.kind === "file" &&
        (item.fetch_status === FetchStatus.Initial ||
          item.fetch_status === FetchStatus.Cancelled)
      ) {
        dispatch(
          updateItemFetchStatus({
            sourceUuid: sourceWithItems.uuid,
            itemUuid: item.uuid,
            fetchStatus: FetchStatus.DownloadInProgress,
            authToken: token,
          }),
        );
      }
    });
  }, [sourceWithItems, session.authData, dispatch, store]);

  // Keyboard shortcut: Ctrl+D downloads all files
  useShortcut("downloadAll", () => downloadAllFiles(), undefined, [
    downloadAllFiles,
  ]);

  const virtualRows = useMemo((): VirtualRow[] => {
    const rows: VirtualRow[] = oldItemIds.map((id) => ({ kind: "item", itemId: id }));
    if (dividerIndex !== null) {
      rows.push({ kind: "divider" });
    }
    newItemIds.forEach((id) => rows.push({ kind: "item", itemId: id }));
    return rows;
  }, [oldItemIds, newItemIds, dividerIndex]);

  // Load older messages when the user scrolls near the top
  useEffect(() => {
    if (!scrollElement) {
      return;
    }

    const handleScroll = () => {
      if (
        scrollElement.scrollTop <= 50 &&
        hasMoreHistoricalItems &&
        !olderItemsLoading &&
        sourceWithItems
      ) {
        dispatch(fetchOlderConversationItems(sourceWithItems.uuid));
      }
    };

    scrollElement.addEventListener("scroll", handleScroll);
    return () => {
      scrollElement.removeEventListener("scroll", handleScroll);
    };
  }, [
    dispatch,
    hasMoreHistoricalItems,
    olderItemsLoading,
    scrollElement,
    sourceWithItems,
  ]);

  if (!sourceWithItems) {
    return null;
  }

  return (
    <div
      className="flex flex-col h-full w-full min-h-0"
      data-testid="conversation-container"
    >
      <div className="flex-1 min-h-0 relative">
        {hasItems ? (
          <List
            data-testid="conversation-items-container"
            rowCount={virtualRows.length}
            rowHeight={dynamicRowHeight}
            rowComponent={ConversationRow}
            rowProps={{ virtualRows, designation: designation || "" }}
            listRef={listRef}
            style={{
              height: "100%",
              visibility: heightsReady ? "visible" : "hidden",
            }}
            className="pt-4"
          />
        ) : (
          <div className="flex items-center justify-center h-full">
            <EmptyConversation />
          </div>
        )}
        {showNewMessagesButton && (
          <Button
            data-testid="new-messages-button"
            size="small"
            onClick={scrollToBottom}
            className="new-messages-notification-btn"
          >
            {t("conversation.newMessagesDivider")} ↓
          </Button>
        )}
      </div>
      <div className="flex-shrink-0 p-4 pt-0">
        <Form form={form} layout="vertical" onFinish={handleSubmit}>
          <div className="relative">
            <Form.Item name="message">
              <Input.TextArea
                data-testid="reply-textarea"
                maxLength={MAX_REPLY_LENGTH}
                placeholder={placeholderText}
                className="w-full border border-gray-300 rounded-lg p-3 text-gray-900 resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 conversation-textarea"
                onChange={(e) => setMessageValue(e.target.value)}
                showCount
              />
            </Form.Item>
            <Button
              data-testid="send-button"
              type="link"
              htmlType="submit"
              disabled={isSendDisabled}
              className="text-blue-600 hover:text-blue-800 font-medium conversation-send-btn"
            >
              {t("conversation.sendButton")}
            </Button>
          </div>
        </Form>
      </div>
    </div>
  );
});

export default Conversation;
