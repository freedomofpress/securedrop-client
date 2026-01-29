import { memo } from "react";
import { useTranslation } from "react-i18next";
import { toTitleCase, formatDateLong } from "../../../utils";
import Avatar from "../../../components/Avatar";
import type { SourceWithItems } from "../../../../types";
import { Flex } from "antd";
import SourceMenu from "./Header/SourceMenu";

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
      <SourceMenu sourceWithItems={sourceWithItems} />
    </Flex>
  );
});

export default Header;
