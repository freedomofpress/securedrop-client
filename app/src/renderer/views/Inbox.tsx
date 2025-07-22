import Sidebar from "../components/Sidebar";
import MainContent from "../components/MainContent";

function InboxView() {
  return (
    <div className="flex h-screen">
      <Sidebar />
      <MainContent />
    </div>
  );
}

export default InboxView;
