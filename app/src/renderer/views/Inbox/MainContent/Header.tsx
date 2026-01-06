import { memo } from "react";
import { useTranslation } from "react-i18next";
import { toTitleCase, formatDateLong } from "../../../utils";
import Avatar from "../../../components/Avatar";
import type { SourceWithItems } from "../../../../types";
import { MenuProps, Dropdown, Button, Flex } from "antd";
import { EllipsisOutlined } from "@ant-design/icons";

const handleMenuClick: MenuProps['onClick'] = (e) => {
  switch (e.key) {
    case "exportTranscript":
      console.log("export transcript...tk");
      break;

    case "printTranscript":
      console.log("print transcript...tk");
      break;
    default:
      break;
  }
};


const items: MenuProps['items'] = [
  {
    key: "exportTranscript",
    label: "Export transcript...",
  },
  {
    key: "printTranscript",
    label: "Print transcript...",
  },
];

const menuProps = {
  items,
  onClick: handleMenuClick,
};


interface HeaderProps {
  sourceUuid?: string;
  loading: boolean;
  sourceWithItems: SourceWithItems | null;
}

const Header = memo(function Header({
  sourceUuid,
  loading,
  sourceWithItems,
}: HeaderProps) {
  const { t, i18n } = useTranslation("MainContent");

  if (!sourceUuid) {
    return <></>;
  }

  if (loading && !sourceWithItems) {
    return <p>{t("loading.header")}</p>;
  }

  if (!sourceWithItems) {
    return <p>{t("sourceNotFound.header")}</p>;
  }

  const designation = toTitleCase(sourceWithItems.data.journalist_designation);
  const formattedLastSeen = formatDateLong(
    sourceWithItems.data.last_updated,
    i18n.language,
  );

  return (
    <Flex justify="space-between" align="center">
      <Flex>
        <Avatar designation={designation} isActive={false} />
        <div className="ml-2">
          <p data-testid="conversation-header-designation">{designation}</p>
          <p
            className="text-sm text-gray-600"
            data-testid="conversation-header-last-activity"
          >
            {t("lastSourceActivity")}: {formattedLastSeen}
          </p>
        </div>
      </Flex>
      <Dropdown menu={menuProps}>
          <Button
            type="text"
            icon={
              <EllipsisOutlined style={{ color: "gray", fontSize: "24px" }} />
            }
          />
      </Dropdown>
    </Flex>
  );
});

export default Header;
