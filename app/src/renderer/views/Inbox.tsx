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
import { setUnauth } from "../features/session/sessionSlice";
import { SyncStatus } from "../../types";
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
      dispatch(syncMetadata(session.authData.token));
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

  return (
    <div className="flex h-screen min-h-0">
      <Sidebar />
      <MainContent />
    </div>
  );
}

export default InboxView;
