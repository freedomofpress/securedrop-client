import type { SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Conversation/Item";
import NewMessagesDivider from "./Conversation/NewMessagesDivider";
import EmptyConversation from "./EmptyConversation";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import { memo, useMemo, useCallback, useState } from "react";
import { useAppDispatch } from "../../../hooks";
import { fetchSources } from "../../../features/sources/sourcesSlice";
import { fetchConversation } from "../../../features/conversation/conversationSlice";
import useConversationScroll from "./Conversation/useConversationScroll";
import "./Conversation.css";

interface ConversationProps {
  sourceWithItems: SourceWithItems | null;
}

const Conversation = memo(function Conversation({
  sourceWithItems,
}: ConversationProps) {
  const { t } = useTranslation("MainContent");
  const dispatch = useAppDispatch();
  const [form] = Form.useForm();
  const [messageValue, setMessageValue] = useState("");
  const {
    acknowledgeNewMessages,
    dividerItemUuid,
    dividerRef,
    hasItems,
    newItems,
    oldItems,
    scrollContainerRef,
  } = useConversationScroll(sourceWithItems);

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
    () => !messageValue || !messageValue.trim(),
    [messageValue],
  );

  const handleSubmit = useCallback(
    async (values: { message: string }) => {
      if (!sourceWithItems || !values.message?.trim()) return;

      // Clear the form immediately for better UX
      form.resetFields();
      setMessageValue("");

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
      } catch (error) {
        console.error("Failed to send reply:", error);
        // Restore the message on error
        form.setFieldsValue({ message: values.message });
        setMessageValue(values.message);
      }
    },
    [acknowledgeNewMessages, dispatch, dividerItemUuid, form, sourceWithItems],
  );

  if (!sourceWithItems) return null;

  return (
    <div className="flex flex-col h-full w-full min-h-0">
      <div className="flex-1 min-h-0 relative">
        {hasItems ? (
          <div
            ref={scrollContainerRef}
            className="absolute inset-0 overflow-y-auto overflow-x-hidden p-4 pb-0"
            data-testid="conversation-items-container"
          >
            {oldItems.map((item) => (
              <Item
                key={item.uuid}
                item={item}
                designation={designation || ""}
              />
            ))}
            {newItems.length > 0 && (
              <>
                <NewMessagesDivider ref={dividerRef} />
                {newItems.map((item) => (
                  <Item
                    key={item.uuid}
                    item={item}
                    designation={designation || ""}
                  />
                ))}
              </>
            )}
          </div>
        ) : (
          <div className="flex items-center justify-center h-full">
            <EmptyConversation />
          </div>
        )}
      </div>
      <div className="flex-shrink-0 p-4 pt-0">
        <Form form={form} layout="vertical" onFinish={handleSubmit}>
          <div className="relative">
            <Form.Item name="message" style={{ marginBottom: 0 }}>
              <Input.TextArea
                data-testid="reply-textarea"
                rows={4}
                placeholder={placeholderText}
                className="w-full border border-gray-300 rounded-lg p-3 text-gray-900 resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 conversation-textarea"
                onChange={(e) => setMessageValue(e.target.value)}
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
