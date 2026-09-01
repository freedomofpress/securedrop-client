import { memo, useCallback, useEffect, useRef, useState } from "react";
import Account from "./Sidebar/Account";
import SourceList from "./Sidebar/SourceList";
import SyncSidebar, {
  SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  SYNC_SIDEBAR_DEFAULT_HEIGHT,
} from "./Sidebar/SyncSidebar";
import SyncSidebarResizer, {
  SYNC_SIDEBAR_RESIZER_HEIGHT,
} from "./Sidebar/SyncSidebarResizer";
import { useSyncSidebarEnabled } from "../../hooks";
import type { FocusedPanel } from "../Inbox";

const SYNC_SIDEBAR_FALLBACK_MAX_HEIGHT = SYNC_SIDEBAR_DEFAULT_HEIGHT;

// Save pixels so the sidebar doesn't cover the bottom of the sourcelist
const SYNC_SIDEBAR_RESERVED_HEIGHT =
  SYNC_SIDEBAR_COLLAPSED_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT;

interface SidebarProps {
  focusedPanel: FocusedPanel;
}

const Sidebar = memo(function Sidebar({ focusedPanel }: SidebarProps) {
  const syncSidebarEnabled = useSyncSidebarEnabled();
  const overlayAreaRef = useRef<HTMLDivElement>(null);

  const [preferredHeight, setPreferredHeight] = useState(
    SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  );
  const [overlayAreaHeight, setOverlayAreaHeight] = useState(0);

  useEffect(() => {
    const overlayArea = overlayAreaRef.current;
    if (!syncSidebarEnabled || !overlayArea) {
      return;
    }
    const observer = new ResizeObserver(([entry]) =>
      setOverlayAreaHeight(entry.contentRect.height),
    );
    observer.observe(overlayArea);
    return () => observer.disconnect();
  }, [syncSidebarEnabled]);

  const maxHeight =
    overlayAreaHeight > 0
      ? Math.max(
          SYNC_SIDEBAR_COLLAPSED_HEIGHT,
          overlayAreaHeight - SYNC_SIDEBAR_RESIZER_HEIGHT,
        )
      : SYNC_SIDEBAR_FALLBACK_MAX_HEIGHT;

  const height = Math.min(preferredHeight, maxHeight);
  const collapsed = height <= SYNC_SIDEBAR_COLLAPSED_HEIGHT;

  const handleToggle = useCallback(() => {
    setPreferredHeight(
      collapsed ? SYNC_SIDEBAR_DEFAULT_HEIGHT : SYNC_SIDEBAR_COLLAPSED_HEIGHT,
    );
  }, [collapsed]);

  return (
    <div className="sd-border-secondary @container w-full flex flex-col h-full min-h-0 border-e">
      <Account />
      <div
        ref={overlayAreaRef}
        className="relative flex flex-1 flex-col min-h-0"
      >
        <div
          className="flex flex-1 flex-col min-h-0"
          style={
            syncSidebarEnabled
              ? { paddingBottom: SYNC_SIDEBAR_RESERVED_HEIGHT }
              : undefined
          }
          data-testid="source-list-area"
        >
          <SourceList focusedPanel={focusedPanel} />
        </div>
        {syncSidebarEnabled && (
          <div
            className="absolute inset-x-0 bottom-0 flex flex-col"
            data-testid="sync-sidebar-overlay"
          >
            <SyncSidebarResizer
              height={height}
              minHeight={SYNC_SIDEBAR_COLLAPSED_HEIGHT}
              maxHeight={maxHeight}
              onHeightChange={setPreferredHeight}
            />
            <SyncSidebar
              height={height}
              collapsed={collapsed}
              onToggle={handleToggle}
            />
          </div>
        )}
      </div>
    </div>
  );
});

export default Sidebar;
