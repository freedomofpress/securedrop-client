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
import { SyncActivity } from "../../../features/sync/syncSlice";
import {
  DownloadDisplayStatus,
  selectDownloadActivity,
  selectRecentDownloads,
  selectSyncSummary,
} from "../../../features/activity/activitySlice";
import ActivitySection from "./ActivitySidebar/ActivitySection";
import AttentionBanner from "./ActivitySidebar/AttentionBanner";
import {
  CompletedDownloadRow,
  DownloadRow,
} from "./ActivitySidebar/DownloadRow";

export const ACTIVITY_SIDEBAR_COLLAPSED_HEIGHT = 48;

export const ACTIVITY_SIDEBAR_DEFAULT_HEIGHT = 320;

const HEADING_ID = "activity-sidebar-heading";
const BODY_ID = "activity-sidebar-body";

const PRESENTATION: Record<
  SyncActivity,
  { icon: LucideIcon; iconClass: string; labelKey: string; spin: boolean }
> = {
  [SyncActivity.SYNCING]: {
    icon: RefreshCw,
    iconClass: "text-blue-500",
    labelKey: "activitySidebar.status.syncing",
    spin: true,
  },
  [SyncActivity.UP_TO_DATE]: {
    icon: CloudCheck,
    iconClass: "text-blue-500",
    labelKey: "activitySidebar.status.upToDate",
    spin: false,
  },
  [SyncActivity.NEEDS_ATTENTION]: {
    icon: CloudAlert,
    iconClass: "text-amber-500",
    labelKey: "activitySidebar.status.needsAttention",
    spin: false,
  },
};

interface ActivitySidebarProps {
  height: number;
  collapsed: boolean;
  onToggle: () => void;
}

const ActivitySidebar = memo(function ActivitySidebar({
  height,
  collapsed,
  onToggle,
}: ActivitySidebarProps) {
  const { t } = useTranslation("Sidebar");
  const activity = useAppSelector(selectSyncSummary);
  const downloads = useAppSelector(selectDownloadActivity);
  const allRecentDownloads = useAppSelector(selectRecentDownloads);

  const stuckDownloads = downloads.filter(
    (download) =>
      download.displayStatus === DownloadDisplayStatus.NEEDS_ATTENTION,
  );
  const activeDownloads = downloads.filter(
    (download) =>
      download.displayStatus !== DownloadDisplayStatus.NEEDS_ATTENTION,
  );
  const recentDownloads = allRecentDownloads.filter(
    (download) => download.kind === "file" && download.filename !== null,
  );

  const isEmpty = downloads.length === 0 && recentDownloads.length === 0;

  const { icon: Icon, iconClass, labelKey, spin } = PRESENTATION[activity];
  const Chevron = collapsed ? ChevronUp : ChevronDown;

  return (
    <section
      style={{ height }}
      aria-labelledby={HEADING_ID}
      data-testid="activity-sidebar"
      data-collapsed={collapsed}
      className="sd-bg-primary sd-border-secondary flex flex-shrink-0 flex-col overflow-hidden border-t"
    >
      <h2 className="flex-shrink-0" id={HEADING_ID}>
        <button
          type="button"
          onClick={onToggle}
          aria-expanded={!collapsed}
          aria-controls={BODY_ID}
          data-testid="activity-sidebar-toggle"
          style={{ height: ACTIVITY_SIDEBAR_COLLAPSED_HEIGHT }}
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
        data-testid="activity-sidebar-body"
        className="sd-bg-secondary min-h-0 flex-1 overflow-y-auto px-4 py-3"
      >
        {isEmpty ? (
          <p className="sd-text-tertiary" data-testid="activity-sidebar-empty">
            {t("activitySidebar.empty")}
          </p>
        ) : (
          <div className="flex flex-col gap-3">
            <AttentionBanner downloads={stuckDownloads} />
            {(activeDownloads.length > 0 || recentDownloads.length > 0) && (
              <ActivitySection
                title={t("activitySidebar.section.downloads")}
                testId="activity-sidebar-downloads"
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
          </div>
        )}
      </div>
    </section>
  );
});

export default ActivitySidebar;
