import type { SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Items/Item";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import "./Items.css";

interface ItemsProps {
  sourceWithItems: SourceWithItems | null;
}

function Items({ sourceWithItems }: ItemsProps) {
  const { t } = useTranslation("MainContent");

  if (!sourceWithItems) return null;

  const designation = sourceWithItems.data.journalistDesignation;

  return (
    <div className="flex flex-col h-full w-full p-4">
      <div className="flex-1 overflow-y-auto pr-1">
        {sourceWithItems.items.map((item) => (
          <Item key={item.uuid} item={item} designation={designation} />
        ))}
      </div>
      <div className="pt-4">
        <Form layout="vertical">
          <Form.Item style={{ marginBottom: 0 }}>
            <div className="relative">
              <Input.TextArea
                rows={4}
                placeholder={t("items.messagePlaceholder", {
                  designation: toTitleCase(designation),
                })}
                className="w-full border border-gray-300 rounded-lg p-3 text-gray-900 resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 items-textarea"
              />
              <Button
                type="link"
                htmlType="submit"
                className="text-blue-600 hover:text-blue-800 font-medium items-send-btn"
              >
                {t("items.sendButton")}
              </Button>
            </div>
          </Form.Item>
        </Form>
      </div>
    </div>
  );
}

export default Items;
