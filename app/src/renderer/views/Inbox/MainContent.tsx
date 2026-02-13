import { useParams } from "react-router";
import { useEffect, useMemo } from "react";

import { useAppDispatch, useAppSelector } from "../../hooks";
import {
  fetchConversation,
  selectConversation,
  selectLastConversation,
} from "../../features/conversation/conversationSlice";
import EmptyState from "./MainContent/EmptyState";
import Conversation from "./MainContent/Conversation";
import Header from "./MainContent/Header";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const dispatch = useAppDispatch();

  const sourceWithItems = useAppSelector((state) =>
    sourceUuid ? selectConversation(state, sourceUuid) : null,
  );

  const lastConversation = useAppSelector(selectLastConversation);

  // Use current data if available, otherwise fall back to the last loaded
  // conversation while a source is selected.
  const displayedSourceWithItems =
    sourceWithItems ?? (sourceUuid ? lastConversation : null);

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
