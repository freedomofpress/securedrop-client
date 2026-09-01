import { describe, it, expect, vi } from "vitest";
import { screen } from "@testing-library/react";
import userEvent from "@testing-library/user-event";

import { renderWithProviders } from "../../../test-component-setup";
import type { RootState } from "../../../store";
import type { SyncState } from "../../../features/sync/syncSlice";
import { SyncStatus } from "../../../../types";
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
      expect(screen.getByText("Sync sidebar placeholder text")).toBeVisible();
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
});
