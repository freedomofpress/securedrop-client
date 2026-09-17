/* eslint-disable react-refresh/only-export-components */
import { memo, useEffect } from "react";
import { useTranslation } from "react-i18next";
import {
  ChevronDown,
  ChevronUp,
  CloudAlert,
  CloudCheck,
  RefreshCw,
} from "lucide-react";
import type { LucideIcon } from "lucide-react";

import { useAppDispatch, useAppSelector } from "../../../hooks";
import { SyncActivity } from "../../../features/sync/syncSlice";
import {
  COMPLETED_EVENT_DISPLAY_MS,
  DownloadDisplayStatus,
  PendingEventDisplayStatus,
  pruneCompletedEvents,
  selectCompletedEvents,
  selectDownloadActivity,
  selectPendingEventActivity,
  selectRecentDownloads,
  selectSyncSummary,
} from "../../../features/syncActivity/syncActivitySlice";
import ActivitySection from "./SyncSidebar/ActivitySection";
import AttentionBanner from "./SyncSidebar/AttentionBanner";
import { CompletedDownloadRow, DownloadRow } from "./SyncSidebar/DownloadRow";
import PendingEventRow, {
  CompletedEventRow,
} from "./SyncSidebar/PendingEventRow";

export const SYNC_SIDEBAR_COLLAPSED_HEIGHT = 48;

export const SYNC_SIDEBAR_DEFAULT_HEIGHT = 320;

const HEADING_ID = "sync-sidebar-heading";
const BODY_ID = "sync-sidebar-body";

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

const SyncSidebar = memo(function SyncSidebar({
  height,
  collapsed,
  onToggle,
}: SyncSidebarProps) {
  const { t } = useTranslation("Sidebar");
  const dispatch = useAppDispatch();
  const activity = useAppSelector(selectSyncSummary);
  const downloads = useAppSelector(selectDownloadActivity);
  const events = useAppSelector(selectPendingEventActivity);
  const completedEvents = useAppSelector(selectCompletedEvents);
  const allRecentDownloads = useAppSelector(selectRecentDownloads);

  // Events often sync faster than the eye can follow, so a drained one lingers
  // briefly before being dropped. Evict on the oldest entry's deadline.
  useEffect(() => {
    const oldest = completedEvents.at(-1);
    if (!oldest) {
      return;
    }
    const timer = setTimeout(
      () =>
        dispatch(pruneCompletedEvents(Date.now() - COMPLETED_EVENT_DISPLAY_MS)),
      Math.max(0, oldest.completedAt + COMPLETED_EVENT_DISPLAY_MS - Date.now()),
    );
    return () => clearTimeout(timer);
  }, [completedEvents, dispatch]);

  // Anything stuck is lifted out of its section and surfaced at the top of
  // the panel, so each list below only carries work that is still moving.
  const stuckDownloads = downloads.filter(
    (download) =>
      download.displayStatus === DownloadDisplayStatus.NEEDS_ATTENTION,
  );
  const stuckEvents = events.filter(
    (event) =>
      event.displayStatus === PendingEventDisplayStatus.NEEDS_ATTENTION,
  );
  const activeDownloads = downloads.filter(
    (download) =>
      download.displayStatus !== DownloadDisplayStatus.NEEDS_ATTENTION,
  );
  const queuedEvents = events.filter(
    (event) =>
      event.displayStatus !== PendingEventDisplayStatus.NEEDS_ATTENTION,
  );
  // Only files can be opened once they land, so other kinds just drop off
  const recentDownloads = allRecentDownloads.filter(
    (download) => download.kind === "file" && download.filename !== null,
  );

  const isEmpty =
    downloads.length === 0 &&
    events.length === 0 &&
    completedEvents.length === 0 &&
    recentDownloads.length === 0;

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

      <div
        id={BODY_ID}
        hidden={collapsed}
        data-testid="sync-sidebar-body"
        className="sd-bg-secondary min-h-0 flex-1 overflow-y-auto px-4 py-3"
      >
        {isEmpty ? (
          <p className="sd-text-tertiary" data-testid="sync-sidebar-empty">
            {t("syncSidebar.empty")}
          </p>
        ) : (
          <div className="flex flex-col gap-3">
            <AttentionBanner events={stuckEvents} downloads={stuckDownloads} />
            {(activeDownloads.length > 0 || recentDownloads.length > 0) && (
              <ActivitySection
                title={t("syncSidebar.section.downloads")}
                testId="sync-sidebar-downloads"
              >
                {activeDownloads.map((download) => (
                  <DownloadRow key={download.itemUuid} download={download} />
                ))}
                {recentDownloads.map((download) => (
                  <CompletedDownloadRow
                    key={download.itemUuid}
                    download={download}
                  />
                ))}
              </ActivitySection>
            )}
            {(queuedEvents.length > 0 || completedEvents.length > 0) && (
              <ActivitySection
                title={t("syncSidebar.section.pending")}
                testId="sync-sidebar-pending"
              >
                {queuedEvents.map((event) => (
                  <PendingEventRow key={event.id} event={event} />
                ))}
                {completedEvents.map((event) => (
                  <CompletedEventRow key={event.id} event={event} />
                ))}
              </ActivitySection>
            )}
          </div>
        )}
      </div>
    </section>
  );
});

export default SyncSidebar;
