import type { SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Conversation/Item";
import NewMessagesDivider from "./Conversation/NewMessagesDivider";
import EmptyConversation from "./EmptyConversation";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import {
  memo,
  useMemo,
  useCallback,
  useState,
  useEffect,
  type ReactElement,
} from "react";
import { useAppDispatch, useAppSelector, useDebounce } from "../../../hooks";
import { fetchSources } from "../../../features/sources/sourcesSlice";
import {
  setDraft,
  clearDraft,
  selectDraft,
} from "../../../features/drafts/draftsSlice";
import {
  fetchConversation,
  updateItemFetchStatus,
} from "../../../features/conversation/conversationSlice";
import { syncMetadata } from "../../../features/sync/syncSlice";
import useConversationScroll from "./Conversation/useConversationScroll";
import "./Conversation.css";
import { FetchStatus } from "../../../../types";
import { List } from "react-window";
import type { RowComponentProps } from "react-window";

const MAX_REPLY_LENGTH = 5000;

interface ConversationProps {
  sourceWithItems: SourceWithItems | null;
}

type VirtualRow =
  | { kind: "item"; item: SourceWithItems["items"][number] }
  | { kind: "divider" };

interface ConversationRowProps {
  virtualRows: VirtualRow[];
  designation: string;
}

const ConversationRow = memo(function ConversationRow({
  index,
  style,
  virtualRows,
  designation,
}: RowComponentProps<ConversationRowProps>): ReactElement {
  const row = virtualRows[index];
  return (
    <div style={style} className="px-4">
      {row.kind === "divider" ? (
        <NewMessagesDivider />
      ) : (
        <Item item={row.item} designation={designation} />
      )}
    </div>
  );
});

const Conversation = memo(function Conversation({
  sourceWithItems,
}: ConversationProps) {
  const { t } = useTranslation("MainContent");
  const dispatch = useAppDispatch();
  const session = useAppSelector((state) => state.session);
  const sourceUuid = sourceWithItems?.uuid ?? "";
  const savedDraft = useAppSelector(selectDraft(sourceUuid));
  const [form] = Form.useForm();
  const [messageValue, setMessageValue] = useState(savedDraft);
  const debouncedMessage = useDebounce(messageValue, 300);
  const {
    acknowledgeNewMessages,
    dividerIndex,
    dividerItemUuid,
    dynamicRowHeight,
    hasItems,
    listRef,
    newItems,
    oldItems,
  } = useConversationScroll(sourceWithItems);

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

      // Calculate the likely interactionCount this reply will be assigned; it
      // may not be correct (e.g. if the conversation was deleted) but it'll display
      // in the correct order while pending and then get adjusted on the server.
      const nextInteractionCount =
        (sourceWithItems.items.at(-1)?.data.interaction_count || 0) + 1;

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
    ],
  );

  // Keyboard shortcut: Ctrl+Enter sends reply
  const sendReply = useCallback(
    (e: React.KeyboardEvent<HTMLTextAreaElement>) => {
      if (e.ctrlKey && e.key === "Enter") {
        e.preventDefault();
        form.submit();
      }
    },
    [form],
  );

  // Keyboard shortcut: Ctrl+D initiates download for all files
  const downloadAllFiles = useCallback(() => {
    if (!sourceWithItems || !session.authData?.token) {
      return;
    }

    const token = session.authData.token;
    sourceWithItems.items.forEach((item) => {
      if (
        item.data.kind === "file" &&
        item.fetch_status === FetchStatus.Initial
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
  }, [sourceWithItems, session.authData, dispatch]);

  useEffect(() => {
    const shortcuts = (e: KeyboardEvent) => {
      if (e.ctrlKey && e.key === "d") {
        e.preventDefault();
        downloadAllFiles();
      }
    };

    document.addEventListener("keydown", shortcuts);
    return () => {
      document.removeEventListener("keydown", shortcuts);
    };
  }, [downloadAllFiles]);

  const virtualRows = useMemo((): VirtualRow[] => {
    const rows: VirtualRow[] = oldItems.map((item) => ({ kind: "item", item }));
    if (dividerIndex !== null) {
      rows.push({ kind: "divider" });
    }
    newItems.forEach((item) => rows.push({ kind: "item", item }));
    return rows;
  }, [oldItems, newItems, dividerIndex]);

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
            style={{ height: "100%" }}
            className="pt-4"
          />
        ) : (
          <div className="flex items-center justify-center h-full">
            <EmptyConversation />
          </div>
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
                onKeyDown={sendReply}
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
