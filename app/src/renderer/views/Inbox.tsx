import { useEffect } from "react";
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

  // Trigger sync in the background every second
  setInterval(() => {
    dispatch(syncMetadata(session.authData?.token));
  }, 1000);

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
