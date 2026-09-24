import { describe, it, expect, vi } from "vitest";
import { screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";

import { renderWithProviders } from "../../../test-component-setup";
import type { RootState } from "../../../store";
import type { SyncState } from "../../../features/sync/syncSlice";
import type { ActivityState } from "../../../features/activity/activitySlice";
import {
  FetchStatus,
  SyncStatus,
  type DownloadActivity,
} from "../../../../types";
import ActivitySidebar, {
  ACTIVITY_SIDEBAR_COLLAPSED_HEIGHT,
  ACTIVITY_SIDEBAR_DEFAULT_HEIGHT,
} from "./ActivitySidebar";

const syncState = (sync: Partial<SyncState>): Partial<RootState> => ({
  sync: {
    error: null,
    lastSyncStarted: null,
    lastSyncFinished: null,
    status: null,
    ...sync,
  },
});

const emptyActivity: ActivityState = {
  downloads: {},
  recentDownloads: [],
  pendingEvents: [],
  inFlightEventIds: [],
  completedEvents: [],
  loading: false,
  error: null,
};

const activityState = (
  activity: Partial<ActivityState>,
): Partial<RootState> => ({
  activity: { ...emptyActivity, ...activity },
});

const makeDownload = (
  overrides: Partial<DownloadActivity> = {},
): DownloadActivity => ({
  itemUuid: "item-1",
  sourceUuid: "source-1",
  sourceDesignation: "crimson falcon",
  filename: "Transcripts.pdf",
  kind: "file",
  fetchStatus: FetchStatus.Initial,
  fetchProgress: null,
  size: 1000,
  decryptedSize: null,
  retryAttempts: 0,
  updatedAt: 1000,
  ...overrides,
});

const downloadsByUuid = (downloads: DownloadActivity[]) =>
  Object.fromEntries(
    downloads.map((download) => [download.itemUuid, download]),
  );

const expanded = {
  collapsed: false,
  height: ACTIVITY_SIDEBAR_DEFAULT_HEIGHT,
};

const renderActivitySidebar = (
  {
    collapsed = true,
    height = ACTIVITY_SIDEBAR_COLLAPSED_HEIGHT,
    onToggle = vi.fn(),
  } = {},
  preloadedState?: Partial<RootState>,
) =>
  renderWithProviders(
    <ActivitySidebar
      collapsed={collapsed}
      height={height}
      onToggle={onToggle}
    />,
    { preloadedState },
  );

describe("ActivitySidebar", () => {
  describe("status", () => {
    it("says it is syncing while a sync is in flight", () => {
      renderActivitySidebar({}, syncState({ lastSyncStarted: 1000 }));

      expect(
        screen.getByRole("heading", { name: "Syncing..." }),
      ).toBeInTheDocument();
    });

    it("says it is caught up once a sync has finished cleanly", () => {
      renderActivitySidebar(
        {},
        syncState({
          lastSyncStarted: 1000,
          lastSyncFinished: 2000,
          status: SyncStatus.UPDATED,
        }),
      );

      expect(
        screen.getByRole("heading", { name: "All caught up" }),
      ).toBeInTheDocument();
    });

    it("says it is caught up before the first sync has been attempted", () => {
      renderActivitySidebar({}, syncState({}));

      expect(
        screen.getByRole("heading", { name: "All caught up" }),
      ).toBeInTheDocument();
    });

    it.each([SyncStatus.ERROR, SyncStatus.TIMEOUT, SyncStatus.FORBIDDEN])(
      "asks for attention after a sync reports %s",
      (status) => {
        renderActivitySidebar(
          {},
          syncState({
            lastSyncStarted: 1000,
            lastSyncFinished: 2000,
            status,
          }),
        );

        expect(
          screen.getByRole("heading", { name: "Needs attention" }),
        ).toBeInTheDocument();
      },
    );

    it("asks for attention when the last sync threw", () => {
      renderActivitySidebar(
        {},
        syncState({
          lastSyncStarted: 1000,
          lastSyncFinished: 2000,
          error: "Failed to sync metadata",
          status: SyncStatus.ERROR,
        }),
      );

      expect(
        screen.getByRole("heading", { name: "Needs attention" }),
      ).toBeInTheDocument();
    });

    it("reports a retry after a failure as syncing, not as an error", () => {
      renderActivitySidebar(
        {},
        syncState({
          lastSyncStarted: 3000,
          lastSyncFinished: 2000,
          error: "Failed to sync metadata",
          status: SyncStatus.ERROR,
        }),
      );

      expect(
        screen.getByRole("heading", { name: "Syncing..." }),
      ).toBeInTheDocument();
    });
  });

  describe("collapsed and expanded states", () => {
    it("shows the status but hides the body when collapsed", () => {
      renderActivitySidebar({ collapsed: true });

      expect(screen.getByTestId("activity-sidebar-toggle")).toHaveAttribute(
        "aria-expanded",
        "false",
      );
      expect(screen.getByTestId("activity-sidebar-body")).not.toBeVisible();
    });

    it("keeps the status as the title and reveals the body when expanded", () => {
      renderActivitySidebar({
        collapsed: false,
        height: ACTIVITY_SIDEBAR_DEFAULT_HEIGHT,
      });

      expect(screen.getByTestId("activity-sidebar-toggle")).toHaveAttribute(
        "aria-expanded",
        "true",
      );
      expect(
        screen.getByRole("heading", { name: "All caught up" }),
      ).toBeInTheDocument();
      expect(screen.getByTestId("activity-sidebar-body")).toBeVisible();
      expect(screen.getByTestId("activity-sidebar-empty")).toBeVisible();
    });

    it("renders at the height it is given", () => {
      renderActivitySidebar({
        collapsed: false,
        height: ACTIVITY_SIDEBAR_DEFAULT_HEIGHT,
      });

      // `getComputedStyle` is stubbed for Ant Design, so read the inline
      // style rather than going through `toHaveStyle`.
      expect(
        screen.getByTestId("activity-sidebar").style.getPropertyValue("height"),
      ).toBe(`${ACTIVITY_SIDEBAR_DEFAULT_HEIGHT}px`);
    });

    it("asks to be toggled when the header is clicked", async () => {
      const onToggle = vi.fn();
      renderActivitySidebar({ onToggle });

      await userEvent.click(screen.getByTestId("activity-sidebar-toggle"));
      expect(onToggle).toHaveBeenCalledOnce();
    });

    it("labels the panel with its status heading", () => {
      renderActivitySidebar({}, syncState({ lastSyncStarted: 1000 }));

      expect(
        screen.getByRole("region", { name: "Syncing..." }),
      ).toBeInTheDocument();
    });
  });

  describe("downloads", () => {
    it("lists each download with its source designation", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([
            makeDownload({
              itemUuid: "item-1",
              fetchStatus: FetchStatus.Initial,
            }),
            makeDownload({
              itemUuid: "item-2",
              filename: "Paystubs.xls",
              sourceDesignation: "robin wayne",
              fetchStatus: FetchStatus.Paused,
            }),
          ]),
        }),
      );

      const downloads = screen.getByTestId("activity-sidebar-downloads");
      expect(within(downloads).getByText("Transcripts.pdf")).toBeVisible();
      expect(within(downloads).getByText("Crimson Falcon")).toBeVisible();
      expect(within(downloads).getByText("Paystubs.xls")).toBeVisible();
      expect(within(downloads).getByText("Robin Wayne")).toBeVisible();
    });

    it("shows how far an in-flight download has got", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([
            makeDownload({
              fetchStatus: FetchStatus.DownloadInProgress,
              fetchProgress: 820,
              size: 1000,
            }),
          ]),
        }),
      );

      expect(screen.getByText("82%")).toBeVisible();
    });

    it("falls back to the status when the server never reported a size", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([
            makeDownload({
              fetchStatus: FetchStatus.DownloadInProgress,
              fetchProgress: 820,
              size: null,
            }),
          ]),
        }),
      );

      expect(screen.getByTestId("sync-status-pill")).toHaveTextContent(
        "Downloading",
      );
    });

    it.each([
      [FetchStatus.Initial, "Queued", "neutral"],
      [FetchStatus.DecryptionInProgress, "Decrypting", "neutral"],
      [FetchStatus.Paused, "Stopped", "warning"],
    ])("badges a %s download as %s", (fetchStatus, label, tone) => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([makeDownload({ fetchStatus })]),
        }),
      );

      const pill = screen.getByTestId("sync-status-pill");
      expect(pill).toHaveTextContent(label);
      expect(pill).toHaveAttribute("data-tone", tone);
    });

    it("offers to open a file that has finished downloading", async () => {
      renderActivitySidebar(
        expanded,
        activityState({
          recentDownloads: [
            makeDownload({
              itemUuid: "item-9",
              filename: "/var/data/Handbook.pdf",
            }),
          ],
        }),
      );

      await userEvent.click(screen.getByTestId("sync-download-open-item-9"));

      expect(window.electronAPI.openFile).toHaveBeenCalledWith("item-9");
    });

    it("drops finished messages and replies, which have no file to open", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          recentDownloads: [
            makeDownload({ itemUuid: "item-9", kind: "message" }),
          ],
        }),
      );

      expect(screen.getByTestId("activity-sidebar-empty")).toBeVisible();
    });

    it("hides the rows when the section is collapsed", async () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([makeDownload()]),
        }),
      );

      await userEvent.click(
        screen.getByTestId("activity-sidebar-downloads-toggle"),
      );

      expect(screen.getByTestId("sync-download-item-1")).not.toBeVisible();
    });
  });

  describe("items that need attention", () => {
    it("lifts a failed download out of the downloads list", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([
            makeDownload({ fetchStatus: FetchStatus.FailedTerminal }),
          ]),
        }),
      );

      expect(screen.getByTestId("sync-attention-item-1")).toHaveTextContent(
        "Transcripts.pdf → Crimson Falcon download failed",
      );
      expect(
        screen.queryByTestId("activity-sidebar-downloads"),
      ).not.toBeInTheDocument();
    });

    it("says a retryable download is still being retried", () => {
      renderActivitySidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([
            makeDownload({
              fetchStatus: FetchStatus.FailedDownloadRetryable,
            }),
          ]),
        }),
      );

      expect(screen.getByTestId("sync-attention-item-1")).toHaveTextContent(
        "download failed, retrying",
      );
    });
  });
});
