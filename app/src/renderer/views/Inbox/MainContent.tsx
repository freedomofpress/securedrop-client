import { useParams } from "react-router";
import { useState, useEffect } from "react";
import type { SourceWithItems } from "../../../types";
import { toTitleCase } from "../../utils";
import Avatar from "../../components/Avatar";
import EmptyState from "./MainContent/EmptyState";
import Items from "./MainContent/Items";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const [sourceWithItems, setSourceWithItems] =
    useState<SourceWithItems | null>(null);
  const [loading, setLoading] = useState(false);

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
      header = <p>Loading...</p>;
      content = <p>Loading source details...</p>;
    } else if (!sourceWithItems) {
      // Source not found
      header = <p>Source Not Found</p>;
      content = <p>Source not found</p>;
    } else {
      // Source found, display items
      const designation = toTitleCase(
        sourceWithItems.data.journalistDesignation,
      );
      header = (
        <>
          <Avatar designation={designation} isActive={false} />
          <p className="ml-2">{designation}</p>
        </>
      );
      content = <Items sourceWithItems={sourceWithItems} />;
    }
  } else {
    // Show empty state when no source is selected
    header = <></>;
    content = <EmptyState />;
  }

  return (
    <div className="flex-1 flex flex-col h-full">
      <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4">
        {header}
      </div>
      <div className="flex-1 flex items-center justify-center sd-bg-secondary">
        {content}
      </div>
    </div>
  );
}

export default MainContent;
