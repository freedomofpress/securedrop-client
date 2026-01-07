import { memo } from "react";
// import { useTranslation } from "react-i18next";
import type { SourceWithItems } from "../../../../types";
import { MenuProps, Dropdown, Button } from "antd";
import { EllipsisOutlined } from "@ant-design/icons";

interface SourceMenuProps {
  sourceUuid: string;
  sourceWithItems: SourceWithItems;
}

const SourceMenu = memo(function SourceMenu({
  sourceUuid,
  sourceWithItems,
}: SourceMenuProps) {
  const handleMenuClick: MenuProps["onClick"] = (e) => {
    switch (e.key) {
      case "exportTranscript":
        console.log(`export transcript for ${sourceUuid}...tk`);
        break;

      case "printTranscript":
        console.log("print transcript...tk");
        break;
      default:
        break;
    }
  };

  const hasConversation: boolean = sourceWithItems.items.length > 0;

  const items: MenuProps["items"] = [
    {
      key: "exportTranscript",
      label: "Export transcript...",
      disabled: !hasConversation,
    },
    {
      key: "printTranscript",
      label: "Print transcript...",
      disabled: !hasConversation,
    },
    {
      type: "divider",
    },
    {
      key: "deleteSource",
      label: "Delete Source",
    },
  ];

  const menuProps = {
    items,
    onClick: handleMenuClick,
  };

  // will need translations at some point
  //  const { t, i18n } = useTranslation("MainContent");

  if (!sourceUuid) {
    return <></>;
  }

  return (
    <Dropdown menu={menuProps}>
      <Button
        type="text"
        icon={<EllipsisOutlined style={{ color: "gray", fontSize: "24px" }} />}
      />
    </Dropdown>
  );
});

export default SourceMenu;
