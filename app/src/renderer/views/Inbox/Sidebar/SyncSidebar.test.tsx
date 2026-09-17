import { describe, it, expect, vi } from "vitest";
import { act, screen, waitFor, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";

import { renderWithProviders } from "../../../test-component-setup";
import type { RootState } from "../../../store";
import type { SyncState } from "../../../features/sync/syncSlice";
import type { SyncActivityState } from "../../../features/syncActivity/syncActivitySlice";
import {
  EventStatus,
  FetchStatus,
  PendingEventType,
  SyncStatus,
  type DownloadActivity,
  type PendingEventActivity,
} from "../../../../types";
import { COMPLETED_EVENT_DISPLAY_MS } from "../../../features/syncActivity/syncActivitySlice";
import SyncSidebar, {
  SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  SYNC_SIDEBAR_DEFAULT_HEIGHT,
} from "./SyncSidebar";

const syncState = (sync: Partial<SyncState>): Partial<RootState> => ({
  sync: {
    error: null,
    lastSyncStarted: null,
    lastSyncFinished: null,
    status: null,
    ...sync,
  },
});

const emptyActivity: SyncActivityState = {
  downloads: {},
  recentDownloads: [],
  pendingEvents: [],
  inFlightEventIds: [],
  submittedEventIds: [],
  completedEvents: [],
  loading: false,
  error: null,
};

const activityState = (
  syncActivity: Partial<SyncActivityState>,
): Partial<RootState> => ({
  syncActivity: { ...emptyActivity, ...syncActivity },
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

const makeEvent = (
  overrides: Partial<PendingEventActivity> = {},
): PendingEventActivity => ({
  id: "event-1",
  type: PendingEventType.SourceConversationTruncated,
  sourceUuid: "source-1",
  itemUuid: null,
  sourceDesignation: "aged sutler",
  filename: null,
  retryAttempts: 0,
  lastEventStatus: null,
  ...overrides,
});

const expanded = {
  collapsed: false,
  height: SYNC_SIDEBAR_DEFAULT_HEIGHT,
};

const renderSyncSidebar = (
  {
    collapsed = true,
    height = SYNC_SIDEBAR_COLLAPSED_HEIGHT,
    onToggle = vi.fn(),
  } = {},
  preloadedState?: Partial<RootState>,
) =>
  renderWithProviders(
    <SyncSidebar collapsed={collapsed} height={height} onToggle={onToggle} />,
    { preloadedState },
  );

describe("SyncSidebar", () => {
  describe("status", () => {
    it("says it is syncing while a sync is in flight", () => {
      renderSyncSidebar({}, syncState({ lastSyncStarted: 1000 }));

      expect(
        screen.getByRole("heading", { name: "Syncing..." }),
      ).toBeInTheDocument();
    });

    it("says it is caught up once a sync has finished cleanly", () => {
      renderSyncSidebar(
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
      renderSyncSidebar({}, syncState({}));

      expect(
        screen.getByRole("heading", { name: "All caught up" }),
      ).toBeInTheDocument();
    });

    it.each([SyncStatus.ERROR, SyncStatus.TIMEOUT, SyncStatus.FORBIDDEN])(
      "asks for attention after a sync reports %s",
      (status) => {
        renderSyncSidebar(
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
      renderSyncSidebar(
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
      renderSyncSidebar(
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
      renderSyncSidebar({ collapsed: true });

      expect(screen.getByTestId("sync-sidebar-toggle")).toHaveAttribute(
        "aria-expanded",
        "false",
      );
      expect(screen.getByTestId("sync-sidebar-body")).not.toBeVisible();
    });

    it("keeps the status as the title and reveals the body when expanded", () => {
      renderSyncSidebar({
        collapsed: false,
        height: SYNC_SIDEBAR_DEFAULT_HEIGHT,
      });

      expect(screen.getByTestId("sync-sidebar-toggle")).toHaveAttribute(
        "aria-expanded",
        "true",
      );
      expect(
        screen.getByRole("heading", { name: "All caught up" }),
      ).toBeInTheDocument();
      expect(screen.getByTestId("sync-sidebar-body")).toBeVisible();
      expect(screen.getByTestId("sync-sidebar-empty")).toBeVisible();
    });

    it("renders at the height it is given", () => {
      renderSyncSidebar({
        collapsed: false,
        height: SYNC_SIDEBAR_DEFAULT_HEIGHT,
      });

      // `getComputedStyle` is stubbed for Ant Design, so read the inline
      // style rather than going through `toHaveStyle`.
      expect(
        screen.getByTestId("sync-sidebar").style.getPropertyValue("height"),
      ).toBe(`${SYNC_SIDEBAR_DEFAULT_HEIGHT}px`);
    });

    it("asks to be toggled when the header is clicked", async () => {
      const onToggle = vi.fn();
      renderSyncSidebar({ onToggle });

      await userEvent.click(screen.getByTestId("sync-sidebar-toggle"));
      expect(onToggle).toHaveBeenCalledOnce();
    });

    it("labels the panel with its status heading", () => {
      renderSyncSidebar({}, syncState({ lastSyncStarted: 1000 }));

      expect(
        screen.getByRole("region", { name: "Syncing..." }),
      ).toBeInTheDocument();
    });
  });

  describe("downloads", () => {
    it("lists each download with its source designation", () => {
      renderSyncSidebar(
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

      const downloads = screen.getByTestId("sync-sidebar-downloads");
      expect(within(downloads).getByText("Transcripts.pdf")).toBeVisible();
      expect(within(downloads).getByText("Crimson Falcon")).toBeVisible();
      expect(within(downloads).getByText("Paystubs.xls")).toBeVisible();
      expect(within(downloads).getByText("Robin Wayne")).toBeVisible();
    });

    it("shows how far an in-flight download has got", () => {
      renderSyncSidebar(
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
      renderSyncSidebar(
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
      renderSyncSidebar(
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
      renderSyncSidebar(
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
      renderSyncSidebar(
        expanded,
        activityState({
          recentDownloads: [
            makeDownload({ itemUuid: "item-9", kind: "message" }),
          ],
        }),
      );

      expect(screen.getByTestId("sync-sidebar-empty")).toBeVisible();
    });

    it("hides the rows when the section is collapsed", async () => {
      renderSyncSidebar(
        expanded,
        activityState({
          downloads: downloadsByUuid([makeDownload()]),
        }),
      );

      await userEvent.click(
        screen.getByTestId("sync-sidebar-downloads-toggle"),
      );

      expect(screen.getByTestId("sync-download-item-1")).not.toBeVisible();
    });
  });

  describe("pending events", () => {
    it("names the change and the source it applies to", () => {
      renderSyncSidebar(
        expanded,
        activityState({ pendingEvents: [makeEvent()] }),
      );

      const pending = screen.getByTestId("sync-sidebar-pending");
      expect(within(pending).getByText("Delete Conversation")).toBeVisible();
      expect(within(pending).getByText("Aged Sutler")).toBeVisible();
      expect(within(pending).getByTestId("sync-status-pill")).toHaveTextContent(
        "Queued",
      );
    });

    it.each([
      [PendingEventType.Starred, "Star"],
      [PendingEventType.Unstarred, "Unstar"],
    ])("tells %s apart from its opposite", (type, label) => {
      renderSyncSidebar(
        expanded,
        activityState({ pendingEvents: [makeEvent({ type })] }),
      );

      expect(
        within(screen.getByTestId("sync-sidebar-pending")).getByText(label),
      ).toBeVisible();
    });

    it("marks the event currently on the wire as sending", () => {
      renderSyncSidebar(
        expanded,
        activityState({
          pendingEvents: [makeEvent({ id: "event-7" })],
          inFlightEventIds: ["event-7"],
        }),
      );

      expect(screen.getByText("Sending")).toBeVisible();
      expect(screen.queryByTestId("sync-status-pill")).not.toBeInTheDocument();
    });

    it("falls back to a placeholder when the source is unknown", () => {
      renderSyncSidebar(
        expanded,
        activityState({
          pendingEvents: [makeEvent({ sourceDesignation: null })],
        }),
      );

      expect(screen.getByText("Unknown source")).toBeVisible();
    });
  });

  describe("events that have finished syncing", () => {
    const completed = (completedAt: number) => ({
      ...makeEvent({ id: "event-9", type: PendingEventType.Starred }),
      completedAt,
    });

    it("keeps a drained event visible next to the queue", () => {
      renderSyncSidebar(
        expanded,
        activityState({
          pendingEvents: [makeEvent({ id: "event-1" })],
          completedEvents: [completed(Date.now())],
        }),
      );

      const pending = screen.getByTestId("sync-sidebar-pending");
      expect(within(pending).getByTestId("sync-event-event-1")).toBeVisible();
      expect(within(pending).getByTestId("sync-event-event-9")).toBeVisible();
      expect(within(pending).getByTestId("sync-event-done")).toHaveTextContent(
        "Done",
      );
    });

    it("shows the section for a drained event even with nothing queued", () => {
      renderSyncSidebar(
        expanded,
        activityState({ completedEvents: [completed(Date.now())] }),
      );

      expect(screen.getByTestId("sync-sidebar-pending")).toBeVisible();
      expect(
        screen.queryByTestId("sync-sidebar-empty"),
      ).not.toBeInTheDocument();
    });

    it("drops the row once it has been shown for long enough", async () => {
      vi.useFakeTimers({ shouldAdvanceTime: true });
      try {
        renderSyncSidebar(
          expanded,
          activityState({ completedEvents: [completed(Date.now())] }),
        );

        expect(screen.getByTestId("sync-event-event-9")).toBeVisible();

        await act(async () => {
          vi.advanceTimersByTime(COMPLETED_EVENT_DISPLAY_MS + 100);
        });

        await waitFor(() =>
          expect(
            screen.queryByTestId("sync-event-event-9"),
          ).not.toBeInTheDocument(),
        );
      } finally {
        vi.useRealTimers();
      }
    });
  });

  describe("items that need attention", () => {
    it("lifts a rejected event out of the pending list and explains why", () => {
      renderSyncSidebar(
        expanded,
        activityState({
          pendingEvents: [
            makeEvent({
              id: "event-3",
              type: PendingEventType.ReplySent,
              sourceDesignation: "cognitive tarsal",
              lastEventStatus: EventStatus.BadRequest,
            }),
          ],
        }),
      );

      expect(screen.getByTestId("sync-attention-event-3")).toHaveTextContent(
        "Reply → Cognitive Tarsal rejected by the server",
      );
      expect(
        screen.queryByTestId("sync-sidebar-pending"),
      ).not.toBeInTheDocument();
    });

    it("lifts a failed download out of the downloads list", () => {
      renderSyncSidebar(
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
        screen.queryByTestId("sync-sidebar-downloads"),
      ).not.toBeInTheDocument();
    });

    it("says a retryable download is still being retried", () => {
      renderSyncSidebar(
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

    it("keeps the rest of the queue visible alongside the banner", () => {
      renderSyncSidebar(
        expanded,
        activityState({
          pendingEvents: [
            makeEvent({ id: "event-3", lastEventStatus: EventStatus.NotFound }),
            makeEvent({ id: "event-4" }),
          ],
        }),
      );

      expect(screen.getByTestId("sync-attention-event-3")).toBeVisible();
      expect(screen.getByTestId("sync-event-event-4")).toBeVisible();
    });
  });
});
