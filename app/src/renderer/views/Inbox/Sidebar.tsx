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
import type { FocusedPanel } from "../Inbox";

// Fallback ceiling for the first render, before the source list area has been
// measured.
const SYNC_SIDEBAR_FALLBACK_MAX_HEIGHT = SYNC_SIDEBAR_DEFAULT_HEIGHT;

// Reserve height so that the sidebar does not cover the bottom of the source list
// when it is collapsed.
const SYNC_SIDEBAR_RESERVED_HEIGHT =
  SYNC_SIDEBAR_COLLAPSED_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT;

interface SidebarProps {
  focusedPanel: FocusedPanel;
}

const Sidebar = memo(function Sidebar({ focusedPanel }: SidebarProps) {
  const overlayAreaRef = useRef<HTMLDivElement>(null);

  // The user's last dragged height. The rendered height clamps this to what
  // fits, so that shrinking and expanding the window restores the panel rather
  // than permanently flattening.
  const [preferredHeight, setPreferredHeight] = useState(
    SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  );
  const [overlayAreaHeight, setOverlayAreaHeight] = useState(0);

  // Track the height of the area the panel overlays, so its ceiling follows
  // window resizes.
  useEffect(() => {
    const overlayArea = overlayAreaRef.current;
    if (!overlayArea) {
      return;
    }
    const observer = new ResizeObserver(([entry]) =>
      setOverlayAreaHeight(entry.contentRect.height),
    );
    observer.observe(overlayArea);
    return () => observer.disconnect();
  }, []);

  // Fully expanded, the panel covers the source list; only the resize handle
  // stays above it, so that it can always be dragged back down.
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
    <div className="sd-border-secondary @container w-full flex flex-col h-full min-h-0 border-r">
      <Account />
      <div
        ref={overlayAreaRef}
        className="relative flex flex-1 flex-col min-h-0"
      >
        {/*
         * The list gives up the collapsed panel's height as real layout space,
         * so its last rows are never stuck underneath the panel. Expanding
         * beyond that overlays the list, which stays scrollable underneath.
         */}
        <div
          className="flex flex-1 flex-col min-h-0"
          style={{ paddingBottom: SYNC_SIDEBAR_RESERVED_HEIGHT }}
          data-testid="source-list-area"
        >
          <SourceList focusedPanel={focusedPanel} />
        </div>
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
      </div>
    </div>
  );
});

export default Sidebar;
