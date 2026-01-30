import { memo, useState } from "react";
import { useTranslation } from "react-i18next";
import {
  type SourceWithItems,
  type ExportPayload,
  type PrintPayload,
  FetchStatus,
} from "../../../../../types";

import { ExportWizard } from "../Conversation/Item/Export";
import { PrintWizard } from "../Conversation/Item/Print";
import { MenuProps, Dropdown, Button, Tooltip } from "antd";
import { MoreOutlined } from "@ant-design/icons";

interface SourceMenuProps {
  sourceWithItems: SourceWithItems;
}

const SourceMenu = memo(function SourceMenu({
  sourceWithItems,
}: SourceMenuProps) {
  const { t } = useTranslation("MainContent");

  const [exportPayload, setExportPayload] = useState<ExportPayload>({
    type: "transcript",
    payload: { source_uuid: sourceWithItems.uuid },
  });

  const printPayload: PrintPayload = {
    type: "transcript",
    payload: { source_uuid: sourceWithItems.uuid },
  };

  const [exportWizardOpen, setExportWizardOpen] = useState(false);
  const [printWizardOpen, setPrintWizardOpen] = useState(false);

  const handleMenuClick: MenuProps["onClick"] = async (e) => {
    switch (e.key) {
      case "exportTranscript":
        try {
          setExportPayload({
            type: "transcript",
            payload: {
              source_uuid: sourceWithItems.uuid,
            },
          });
          setExportWizardOpen(true);
        } catch (error) {
          console.error("Failed to export:", error);
        }
        break;
      case "exportSource":
        try {
          setExportPayload({
            type: "source",
            payload: {
              source_uuid: sourceWithItems.uuid,
              undownloaded_items:
                sourceWithItems.items.filter(
                  (i) => i.fetch_status !== FetchStatus.Complete,
                ).length > 0,
            },
          });
          setExportWizardOpen(true);
        } catch (error) {
          console.error("Failed to export:", error);
        }
        break;

      case "printTranscript":
        try {
          setPrintWizardOpen(true);
        } catch (error) {
          console.error("Failed to print transcript:", error);
        }
        break;
      default:
        break;
    }
  };

  const handleExportWizardClose = () => {
    setExportWizardOpen(false);
  };

  const handlePrintWizardClose = () => {
    setPrintWizardOpen(false);
  };

  const hasConversation: boolean = sourceWithItems.items.length > 0;

  const items: MenuProps["items"] = [
    {
      key: "exportTranscript",
      label: t("menu.exportTranscript"),
      disabled: !hasConversation,
    },
    {
      key: "exportSource",
      label: t("menu.exportSource"),
      disabled: !hasConversation,
    },
    {
      key: "printTranscript",
      label: t("menu.printTranscript"),
      disabled: !hasConversation,
    },
  ];

  const menuProps = {
    items,
    onClick: handleMenuClick,
  };

  if (!sourceWithItems) {
    return <></>;
  }

  return (
    <>
      <Tooltip title={t("menu.clickToOpen")} placement="left">
        <Dropdown menu={menuProps} trigger={["click"]}>
          <Button
            type="text"
            icon={<MoreOutlined style={{ color: "gray", fontSize: "20px" }} />}
          />
        </Dropdown>
      </Tooltip>
      <ExportWizard
        key={exportPayload.type}
        item={exportPayload}
        open={exportWizardOpen}
        onClose={handleExportWizardClose}
      />
      <PrintWizard
        item={printPayload}
        open={printWizardOpen}
        onClose={handlePrintWizardClose}
      />
    </>
  );
});

export default SourceMenu;
