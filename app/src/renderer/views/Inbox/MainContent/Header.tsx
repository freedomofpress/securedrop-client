import { useTranslation } from "react-i18next";
import { toTitleCase } from "../../../utils";
import Avatar from "../../../components/Avatar";
import type { SourceWithItems } from "../../../../types";

interface HeaderProps {
  sourceUuid?: string;
  loading: boolean;
  sourceWithItems: SourceWithItems | null;
}

function Header({ sourceUuid, loading, sourceWithItems }: HeaderProps) {
  const { t } = useTranslation("MainContent");

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

  return (
    <>
      <Avatar designation={designation} isActive={false} />
      <p className="ml-2">{designation}</p>
    </>
  );
}

export default Header;
