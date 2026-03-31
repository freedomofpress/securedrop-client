import { memo } from "react";
import Account from "./Sidebar/Account";
import SourceList from "./Sidebar/SourceList";
import type { FocusedPanel } from "../Inbox";

interface SidebarProps {
  focusedPanel: FocusedPanel;
}

const Sidebar = memo(function Sidebar({ focusedPanel }: SidebarProps) {
  return (
    <div className="sd-border-secondary w-96 flex flex-col h-full min-h-0 border-r">
      <Account />
      <SourceList focusedPanel={focusedPanel} />
    </div>
  );
});

export default Sidebar;
