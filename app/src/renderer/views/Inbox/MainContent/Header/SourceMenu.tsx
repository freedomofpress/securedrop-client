import { memo, useState, useMemo } from "react";
import { useTranslation } from "react-i18next";
import { useStore } from "react-redux";
import {
  type SourceWithItems,
  type ExportPayload,
  type PrintPayload,
  FetchStatus,
} from "../../../../../types";
import {
  selectItemIds,
} from "../../../../features/conversation/conversationSlice";
import { useAppSelector } from "../../../../hooks";
import type { RootState } from "../../../../store";

import { ExportWizard } from "../Conversation/Item/Export";
import { PrintWizard } from "../Conversation/Item/Print";
import { MenuProps, Dropdown, Button, Tooltip } from "antd";
import { MoreOutlined } from "@ant-design/icons";

interface SourceMenuProps {
  sourceWithItems: Omit<SourceWithItems, "items">;
}

const SourceMenu = memo(function SourceMenu({
  sourceWithItems,
}: SourceMenuProps) {
  const { t } = useTranslation("MainContent");
  const store = useStore<RootState>();

  const [exportType, setExportType] = useState<"transcript" | "source">(
    "transcript",
  );
  const [exportWizardKey, setExportWizardKey] = useState(0);

  const exportPayload = useMemo((): ExportPayload => {
    if (exportType === "source") {
      return {
        type: "source",
        payload: {
          source_uuid: sourceWithItems.uuid,
          undownloaded_items: sourceWithItems.items.some(
            (i) =>
              i.data.kind === "file" && i.fetch_status !== FetchStatus.Complete,
          ),
        },
      };
    }
    return {
      type: "transcript",
      payload: { source_uuid: sourceWithItems.uuid },
    };
  }, [exportType, sourceWithItems]);

  const printPayload: PrintPayload = {
    type: "transcript",
    payload: { source_uuid: sourceWithItems.uuid },
  };

  const [exportWizardOpen, setExportWizardOpen] = useState(false);
  const [printWizardOpen, setPrintWizardOpen] = useState(false);

  // Subscribe to itemIds (stable on data updates) rather than the full items
  // array, so SourceMenu only re-renders when items are added or removed.
  const itemIds = useAppSelector(selectItemIds);
  const hasConversation = itemIds.length > 0;

  const handleMenuClick: MenuProps["onClick"] = async (e) => {
    switch (e.key) {
      case "exportTranscript":
        try {
          setExportType("transcript");
          setExportWizardKey((k) => k + 1);
          setExportWizardOpen(true);
        } catch (error) {
          console.error("Failed to export:", error);
        }
        break;
      case "exportSource":
        try {
          // Read item data from store at click time to avoid stale closure.
          const { itemIds: currentIds, itemsById } =
            store.getState().conversation;
          const undownloaded_items = currentIds.some(
            (id) => itemsById[id]?.fetch_status !== FetchStatus.Complete,
          );
          setExportPayload({
            type: "source",
            payload: {
              source_uuid: sourceWithItems.uuid,
              undownloaded_items,
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
        key={exportWizardKey}
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
