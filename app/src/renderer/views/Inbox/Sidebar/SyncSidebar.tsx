/* eslint-disable react-refresh/only-export-components */
import { memo } from "react";
import { useTranslation } from "react-i18next";
import {
  ChevronDown,
  ChevronUp,
  CloudAlert,
  CloudCheck,
  RefreshCw,
} from "lucide-react";
import type { LucideIcon } from "lucide-react";

import { useAppSelector } from "../../../hooks";
import {
  SyncActivity,
  selectSyncActivity,
} from "../../../features/sync/syncSlice";

// Height of the header row, and so of the whole panel when collapsed.
export const SYNC_SIDEBAR_COLLAPSED_HEIGHT = 48;

// Height the panel pops up to the first time it is expanded.
export const SYNC_SIDEBAR_DEFAULT_HEIGHT = 320;

// Sidebar height the panel always leaves to the source list, so expanding it
// can never squeeze the list's toolbar and counts out of the layout.
export const SOURCE_LIST_MIN_HEIGHT = 200;

const HEADING_ID = "sync-sidebar-heading";
const BODY_ID = "sync-sidebar-body";

// How each sync state reads in the header. The header doubles as the status
// line when collapsed and as the panel's title when expanded, so there is a
// single label per state rather than one of each.
const PRESENTATION: Record<
  SyncActivity,
  { icon: LucideIcon; iconClass: string; labelKey: string; spin: boolean }
> = {
  [SyncActivity.SYNCING]: {
    icon: RefreshCw,
    iconClass: "text-blue-500",
    labelKey: "syncSidebar.status.syncing",
    spin: true,
  },
  [SyncActivity.UP_TO_DATE]: {
    icon: CloudCheck,
    iconClass: "text-blue-500",
    labelKey: "syncSidebar.status.upToDate",
    spin: false,
  },
  [SyncActivity.NEEDS_ATTENTION]: {
    icon: CloudAlert,
    iconClass: "text-amber-500",
    labelKey: "syncSidebar.status.needsAttention",
    spin: false,
  },
};

interface SyncSidebarProps {
  height: number;
  collapsed: boolean;
  onToggle: () => void;
}

/**
 * Sync activity panel pinned to the bottom of the sidebar.
 *
 * Collapsed it is a status bar; expanded it keeps that status as its title and
 * reveals the body. The panel's height is owned by `Sidebar`, which also
 * renders the resize handle above it, so the panel and the source list share
 * the sidebar's height rather than overlapping.
 */
const SyncSidebar = memo(function SyncSidebar({
  height,
  collapsed,
  onToggle,
}: SyncSidebarProps) {
  const { t } = useTranslation("Sidebar");
  const activity = useAppSelector(selectSyncActivity);

  const { icon: Icon, iconClass, labelKey, spin } = PRESENTATION[activity];
  const Chevron = collapsed ? ChevronUp : ChevronDown;

  return (
    <section
      style={{ height }}
      aria-labelledby={HEADING_ID}
      data-testid="sync-sidebar"
      data-collapsed={collapsed}
      className="sd-bg-primary sd-border-secondary flex flex-shrink-0 flex-col overflow-hidden border-t"
    >
      <h2 className="flex-shrink-0" id={HEADING_ID}>
        <button
          type="button"
          onClick={onToggle}
          aria-expanded={!collapsed}
          aria-controls={BODY_ID}
          data-testid="sync-sidebar-toggle"
          style={{ height: SYNC_SIDEBAR_COLLAPSED_HEIGHT }}
          className="flex w-full cursor-pointer items-center gap-2 px-4 outline-0 hover:bg-gray-50 focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2"
        >
          <Icon
            size={18}
            strokeWidth={1.5}
            aria-hidden="true"
            className={`${iconClass} ${spin ? "animate-spin" : ""}`}
          />
          <span className="flex-1 text-start text-sm font-semibold">
            {t(labelKey)}
          </span>
          <Chevron size={16} strokeWidth={1.5} aria-hidden="true" />
        </button>
      </h2>

      {/* Placeholder body: the sync event list lands here in a follow-up. */}
      <div
        id={BODY_ID}
        hidden={collapsed}
        data-testid="sync-sidebar-body"
        className="sd-text-tertiary min-h-0 flex-1 overflow-y-auto px-4 py-3 text-sm"
      >
        {t("syncSidebar.body")}
      </div>
    </section>
  );
});

export default SyncSidebar;
