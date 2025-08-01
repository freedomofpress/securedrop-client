import Account from "./Sidebar/Account";
import Sources from "./Sidebar/Sources";

function Sidebar() {
  return (
    <div className="sd-border-secondary w-90 flex flex-col h-full min-h-0 border-r">
      <Account />
      <Sources />
    </div>
  );
}

export default Sidebar;
