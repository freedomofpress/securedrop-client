import { useParams } from "react-router";
import { useState, useEffect } from "react";
import type { SourceWithItems } from "../../../types";
import { toTitleCase } from "../../utils";
import emptyStateImage from "../../../../resources/images/inbox-empty-state.svg";
import "./MainContent.css";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const [sourceWithItems, setSourceWithItems] =
    useState<SourceWithItems | null>(null);
  const [loading, setLoading] = useState(false);

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

  // If we have a source UUID, show the source content
  if (sourceUuid) {
    if (loading) {
      return (
        <div className="flex-1 flex flex-col h-full">
          <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4">
            <p>Loading...</p>
          </div>
          <div className="flex-1 flex items-center justify-center sd-bg-secondary">
            <p>Loading source details...</p>
          </div>
        </div>
      );
    }

    if (!sourceWithItems) {
      return (
        <div className="flex-1 flex flex-col h-full">
          <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4">
            <p>Source Not Found</p>
          </div>
          <div className="flex-1 flex items-center justify-center sd-bg-secondary">
            <p>Source not found</p>
          </div>
        </div>
      );
    }

    const designation = toTitleCase(sourceWithItems.data.journalistDesignation);

    return (
      <div className="flex-1 flex flex-col h-full">
        <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4">
          <p>{designation}</p>
        </div>

        <div className="flex-1 flex items-center justify-center sd-bg-secondary">
          <p>TODO: implement</p>
        </div>
      </div>
    );
  }

  // Show empty state when no source is selected
  return (
    <div className="flex-1 flex flex-col h-full">
      <div className="sd-bg-primary sd-border-secondary border-b h-12">
        {/* Empty header for now */}
      </div>

      <div className="flex-1 flex items-center justify-center sd-bg-secondary">
        <div className="text-center">
          {/* Empty state */}
          <img
            src={emptyStateImage}
            alt="Empty inbox"
            className="w-32 h-32 mx-auto mb-4"
          />

          <p className="sd-text-tertiary empty-state-text">
            <strong>Select a source</strong> from the list to read messages,
            retrieve files, or send responses.
          </p>
        </div>
      </div>
    </div>
  );
}

export default MainContent;
