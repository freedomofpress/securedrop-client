import { useEffect, useCallback } from "react";
import { useDispatch } from "react-redux";
import type { AppDispatch } from "../store";
import { fetchJournalists } from "../features/journalists/journalistsSlice";
import { syncMetadata } from "../features/sync/syncSlice";
import { useAppSelector } from "../hooks";
import Sidebar from "./Inbox/Sidebar";
import MainContent from "./Inbox/MainContent";

function InboxView() {
  const dispatch = useDispatch<AppDispatch>();
  const session = useAppSelector((state) => state.session);

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
