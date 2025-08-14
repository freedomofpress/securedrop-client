import Account from "./Sidebar/Account";
import SourceList from "./Sidebar/SourceList";

function Sidebar() {
  return (
    <div className="sd-border-secondary w-90 flex flex-col h-full min-h-0 border-r">
      <Account />
      <SourceList />
    </div>
  );
}

export default Sidebar;
