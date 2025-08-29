import { useTranslation } from "react-i18next";
import { toTitleCase, normalizeLocale } from "../../../utils";
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
  const lastUpdated = new Date(sourceWithItems.data.last_updated);
  const normalizedLocale = normalizeLocale(i18n.language);
  const formattedLastSeen = new Intl.DateTimeFormat(normalizedLocale, {
    year: 'numeric',
    month: 'short',
    day: 'numeric',
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    timeZoneName: 'short'
  }).format(lastUpdated);

  return (
    <>
      <Avatar designation={designation} isActive={false} />
      <div className="ml-2">
        <p>{designation}</p>
        <p className="text-sm text-gray-600">Last seen: {formattedLastSeen}</p>
      </div>
    </>
  );
}

export default Header;
