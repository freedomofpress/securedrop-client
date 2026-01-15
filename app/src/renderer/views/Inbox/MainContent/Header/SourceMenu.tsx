import { memo, useState } from "react";
// import { useTranslation } from "react-i18next";
import type { SourceWithItems, ExportPayload } from "../../../../../types";
import { ExportWizard } from "../Conversation/Item/Export";
import { MenuProps, Dropdown, Button } from "antd";
import { MoreOutlined } from "@ant-design/icons";

interface SourceMenuProps {
  sourceWithItems: SourceWithItems;
}

const SourceMenu = memo(function SourceMenu({
  sourceWithItems,
}: SourceMenuProps) {
  const [exportWizardOpen, setExportWizardOpen] = useState(false);
  const handleMenuClick: MenuProps["onClick"] = async (e) => {
    switch (e.key) {
      case "exportTranscript":
        try {
          setExportWizardOpen(true);
        } catch (error) {
          console.error("Failed to write transcript:", error);
        }
        console.log(`exporting transcript for ${sourceWithItems.uuid}...tk`);
        break;

      case "printTranscript":
        console.log("print transcript...tk");
        break;
      default:
        break;
    }
  };

  const handleExportWizardClose = () => {
    setExportWizardOpen(false);
    // Note: ExportWizard handles state cleanup via its useEffect when open changes
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

  if (!sourceWithItems) {
    return <></>;
  }

  const exportPayload: ExportPayload = {
    type: "transcript",
    payload: sourceWithItems,
  };

  return (
    <>
      <Dropdown menu={menuProps}>
        <Button
          type="text"
          icon={<MoreOutlined style={{ color: "gray", fontSize: "20px" }} />}
        />
      </Dropdown>
      <ExportWizard
        item={exportPayload}
        open={exportWizardOpen}
        onClose={handleExportWizardClose}
      />
    </>
  );
});

export default SourceMenu;
