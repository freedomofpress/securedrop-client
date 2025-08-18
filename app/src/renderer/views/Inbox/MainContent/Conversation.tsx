import type { SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Conversation/Item";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import { useEffect, useRef } from "react";
import "./Conversation.css";

interface ConversationProps {
  sourceWithItems: SourceWithItems | null;
}

function Conversation({ sourceWithItems }: ConversationProps) {
  const { t } = useTranslation("MainContent");
  const scrollContainerRef = useRef<HTMLDivElement>(null);

  // Scroll to bottom when component mounts or items change
  useEffect(() => {
    if (scrollContainerRef.current && sourceWithItems?.items) {
      scrollContainerRef.current.scrollTop =
        scrollContainerRef.current.scrollHeight;
    }
  }, [sourceWithItems?.items]);

  if (!sourceWithItems) return null;

  const designation = sourceWithItems.data.journalist_designation;

  return (
    <div className="flex flex-col h-full w-full min-h-0">
      <div className="flex-1 min-h-0 relative">
        <div
          ref={scrollContainerRef}
          className="absolute inset-0 overflow-y-auto p-4 pb-0"
        >
          {sourceWithItems.items.map((item) => (
            <Item key={item.uuid} item={item} designation={designation} />
          ))}
        </div>
      </div>
      <div className="flex-shrink-0 p-4 pt-0">
        <Form layout="vertical">
          <Form.Item style={{ marginBottom: 0 }}>
            <div className="relative">
              <Input.TextArea
                rows={4}
                placeholder={t("conversation.messagePlaceholder", {
                  designation: toTitleCase(designation),
                })}
                className="w-full border border-gray-300 rounded-lg p-3 text-gray-900 resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 conversation-textarea"
              />
              <Button
                type="link"
                htmlType="submit"
                className="text-blue-600 hover:text-blue-800 font-medium conversation-send-btn"
              >
                {t("conversation.sendButton")}
              </Button>
            </div>
          </Form.Item>
        </Form>
      </div>
    </div>
  );
}

export default Conversation;
