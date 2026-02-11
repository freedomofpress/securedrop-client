import { useParams } from "react-router";
import { useEffect, useMemo, useState } from "react";

import { useAppDispatch, useAppSelector } from "../../hooks";
import {
  fetchConversation,
  selectConversation,
  selectConversationLoading,
} from "../../features/conversation/conversationSlice";
import type { SourceWithItems } from "../../../types";
import EmptyState from "./MainContent/EmptyState";
import Conversation from "./MainContent/Conversation";
import Header from "./MainContent/Header";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const dispatch = useAppDispatch();

  const sourceWithItems = useAppSelector((state) =>
    sourceUuid ? selectConversation(state, sourceUuid) : null,
  );
  const loading = useAppSelector(selectConversationLoading);

  // Keep the previous sourceWithItems visible while loading the next one.
  const [prevSourceWithItems, setPrevSourceWithItems] =
    useState<SourceWithItems | null>(null);
  if (sourceWithItems && sourceWithItems !== prevSourceWithItems) {
    setPrevSourceWithItems(sourceWithItems);
  } else if (!sourceUuid && prevSourceWithItems !== null) {
    setPrevSourceWithItems(null);
  }

  // Use current data if available, otherwise fall back to previous while loading
  const displayedSourceWithItems =
    sourceWithItems ?? (loading ? prevSourceWithItems : null);

  // Fetch the source with its items
  useEffect(() => {
    if (sourceUuid) {
      dispatch(fetchConversation(sourceUuid));
    }
  }, [dispatch, sourceUuid]);

  const content = useMemo(() => {
    // If we have a source, show the source content
    if (sourceUuid && displayedSourceWithItems) {
      return <Conversation sourceWithItems={displayedSourceWithItems} />;
    } else {
      // Otherwise show empty state
      return (
        <div className="flex flex-1 items-center justify-center w-full h-full">
          <EmptyState />
        </div>
      );
    }
  }, [sourceUuid, displayedSourceWithItems]);

  return (
    <div className="flex-1 flex flex-col h-full min-h-0">
      <div className="sd-bg-primary sd-border-secondary border-b h-12 p-1 px-4">
        <Header
          sourceUuid={sourceUuid}
          sourceWithItems={displayedSourceWithItems}
        />
      </div>
      <div className="flex-1 flex w-full sd-bg-secondary min-h-0">
        {content}
      </div>
    </div>
  );
}

export default MainContent;
