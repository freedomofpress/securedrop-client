import { useParams } from "react-router";
import { useState, useEffect } from "react";
import { useTranslation } from "react-i18next";

import type { SourceWithItems } from "../../../types";
import { toTitleCase } from "../../utils";
import Avatar from "../../components/Avatar";
import EmptyState from "./MainContent/EmptyState";
import Conversation from "./MainContent/Conversation";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const [sourceWithItems, setSourceWithItems] =
    useState<SourceWithItems | null>(null);
  const [loading, setLoading] = useState(false);
  const { t } = useTranslation("MainContent");

  // Fetch the source with its items
  useEffect(() => {
    if (sourceUuid) {
      setLoading(true);
      window.electronAPI
        .getSourceWithItems(sourceUuid)
        .then((sourceWithItems) => {
          setSourceWithItems(sourceWithItems);
          setLoading(false);
        })
        .catch(() => {
          setSourceWithItems(null);
          setLoading(false);
        });
    } else {
      setSourceWithItems(null);
    }
  }, [sourceUuid]);

  let header: React.ReactNode = null;
  let content: React.ReactNode = null;

  // If we have a source UUID, show the source content
  if (sourceUuid) {
    if (loading) {
      // Loading
      header = <p>{t("loading.header")}</p>;
      content = <p>{t("loading.content")}</p>;
    } else if (!sourceWithItems) {
      // Source not found
      header = <p>{t("sourceNotFound.header")}</p>;
      content = <p>{t("sourceNotFound.content")}</p>;
    } else {
      // Source found, display items
      const designation = toTitleCase(
        sourceWithItems.data.journalist_designation,
      );
      header = (
        <>
          <Avatar designation={designation} isActive={false} />
          <p className="ml-2">{designation}</p>
        </>
      );
      content = <Conversation sourceWithItems={sourceWithItems} />;
    }
  } else {
    // Show empty state when no source is selected
    header = <></>;
    content = (
      <div className="flex flex-1 items-center justify-center w-full h-full">
        <EmptyState />
      </div>
    );
  }

  return (
    <div className="flex-1 flex flex-col h-full min-h-0">
      <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4 flex-shrink-0">
        {header}
      </div>
      <div className="flex-1 flex w-full sd-bg-secondary min-h-0">
        {content}
      </div>
    </div>
  );
}

export default MainContent;
