import { useEffect } from "react";
import { useDispatch } from "react-redux";
import type { AppDispatch } from "../store";
import { fetchJournalists } from "../features/journalists/journalistsSlice";
import Sidebar from "./Inbox/Sidebar";
import MainContent from "./Inbox/MainContent";

function InboxView() {
  const dispatch = useDispatch<AppDispatch>();

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
