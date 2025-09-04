import { useTranslation } from "react-i18next";
import { toTitleCase, formatDateLong } from "../../../utils";
import Avatar from "../../../components/Avatar";
import type { SourceWithItems } from "../../../../types";

interface HeaderProps {
  sourceUuid?: string;
  loading: boolean;
  sourceWithItems: SourceWithItems | null;
}

function Header({ sourceUuid, loading, sourceWithItems }: HeaderProps) {
  const { t, i18n } = useTranslation("MainContent");

  if (!sourceUuid) {
    return <></>;
  }

  if (loading) {
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
    <>
      <Avatar designation={designation} isActive={false} />
      <div className="ml-2">
        <p>{designation}</p>
        <p className="text-sm text-gray-600">
          {t("lastSourceActivity")}: {formattedLastSeen}
        </p>
      </div>
    </>
  );
}

export default Header;
