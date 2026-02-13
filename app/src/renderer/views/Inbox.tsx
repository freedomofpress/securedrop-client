import { useEffect, useCallback } from "react";
import { useDispatch } from "react-redux";
import { useTranslation } from "react-i18next";
import type { AppDispatch } from "../store";
import { fetchJournalists } from "../features/journalists/journalistsSlice";
import {
  syncMetadata,
  selectSyncStatus,
  clearStatus,
} from "../features/sync/syncSlice";
import { updateItem } from "../features/conversation/conversationSlice";
import { updateSource } from "../features/sources/sourcesSlice";
import { setUnauth } from "../features/session/sessionSlice";
import { SyncStatus, type Item, type Source } from "../../types";
import { useAppSelector } from "../hooks";
import Sidebar from "./Inbox/Sidebar";
import MainContent from "./Inbox/MainContent";

function InboxView() {
  const dispatch = useDispatch<AppDispatch>();
  const { t } = useTranslation("SignIn");
  const session = useAppSelector((state) => state.session);
  const syncStatus = useAppSelector(selectSyncStatus);

  const sync = useCallback(() => {
    if (session.authData && import.meta.env.MODE != "test") {
      const hintedRecords =
        (session.authData.lastHintedSources || 0) +
        (session.authData.lastHintedItems || 0);
      dispatch(
        syncMetadata({ authToken: session.authData.token, hintedRecords }),
      );
    }
  }, [dispatch, session.authData]);

  // Trigger sync in the background every minute
  useEffect(() => {
    // Trigger immediately
    sync();
    const syncInterval = setInterval(() => {
      sync();
    }, 1000 * 60);

    // Clean up interval
    return () => {
      clearInterval(syncInterval);
    };
  }, [sync]);

  // Handle 403 Forbidden errors from sync
  useEffect(() => {
    if (syncStatus === SyncStatus.FORBIDDEN) {
      dispatch(setUnauth(t("errors.sessionExpired")));
      dispatch(clearStatus());
    }
  }, [syncStatus, dispatch, t]);

  useEffect(() => {
    dispatch(fetchJournalists());
  }, [dispatch]);

  // Register IPC listeners for real-time updates from the main process
  useEffect(() => {
    const unsubscribeItem = window.electronAPI.onItemUpdate((item: Item) => {
      dispatch(updateItem(item));
    });
    const unsubscribeSource = window.electronAPI.onSourceUpdate(
      (source: Source) => {
        dispatch(updateSource(source));
      },
    );
    return () => {
      unsubscribeItem();
      unsubscribeSource();
    };
  }, [dispatch]);

  return (
    <div className="flex h-screen min-h-0">
      <Sidebar />
      <MainContent />
    </div>
  );
}

export default InboxView;
