import Sidebar from "./Inbox/Sidebar";
import MainContent from "./Inbox/MainContent";

function InboxView() {
  return (
    <div className="flex h-screen">
      <Sidebar />
      <MainContent />
    </div>
  );
}

export default InboxView;
