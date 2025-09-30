import { useParams } from "react-router";
import { useEffect, useMemo, useCallback } from "react";
import { useTranslation } from "react-i18next";

import { useAppDispatch, useAppSelector } from "../../hooks";
import {
  fetchConversation,
  selectConversation,
  selectConversationLoading,
  updateItemFetchStatus,
} from "../../features/conversation/conversationSlice";
import EmptyState from "./MainContent/EmptyState";
import Conversation from "./MainContent/Conversation";
import Header from "./MainContent/Header";
import { ItemUpdate, ItemUpdateType } from "../../../../src/types";

function MainContent() {
  const { sourceUuid } = useParams<{ sourceUuid?: string }>();
  const dispatch = useAppDispatch();
  const session = useAppSelector((state) => state.session);
  const { t } = useTranslation("MainContent");

  const sourceWithItems = useAppSelector((state) =>
    sourceUuid ? selectConversation(state, sourceUuid) : null,
  );
  const loading = useAppSelector(selectConversationLoading);

  // Fetch the source with its items
  useEffect(() => {
    if (sourceUuid) {
      dispatch(fetchConversation(sourceUuid));
    }
  }, [dispatch, sourceUuid]);

  const onItemUpdate = useCallback(
    (update: ItemUpdate) => {
      switch (update.type) {
        case ItemUpdateType.FetchStatus:
          dispatch(
            updateItemFetchStatus({
              sourceUuid: sourceUuid ?? "",
              itemUuid: update.item_uuid,
              fetchStatus: update.fetch_status!,
              authToken: session.authData?.token,
            }),
          );
          break;
      }
    },
    [dispatch, sourceUuid, session.authData?.token],
  );

  const content = useMemo(() => {
    // If we have a source UUID, show the source content
    if (sourceUuid) {
      if (loading) {
        // Loading
        return <p>{t("loading.content")}</p>;
      } else if (!sourceWithItems) {
        // Source not found
        return <p>{t("sourceNotFound.content")}</p>;
      } else {
        // Source found, display items
        return (
          <Conversation
            sourceWithItems={sourceWithItems}
            onItemUpdate={onItemUpdate}
          />
        );
      }
    } else {
      // Show empty state when no source is selected
      return (
        <div className="flex flex-1 items-center justify-center w-full h-full">
          <EmptyState />
        </div>
      );
    }
  }, [sourceUuid, loading, sourceWithItems, t, onItemUpdate]);

  return (
    <div className="flex-1 flex flex-col h-full min-h-0">
      <div className="sd-bg-primary sd-border-secondary border-b h-12 flex items-center px-4 flex-shrink-0">
        <Header
          sourceUuid={sourceUuid}
          loading={loading}
          sourceWithItems={sourceWithItems}
        />
      </div>
      <div className="flex-1 flex w-full sd-bg-secondary min-h-0">
        {content}
      </div>
    </div>
  );
}

export default MainContent;
