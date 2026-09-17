import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { screen, fireEvent, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";

import { renderWithProviders } from "../../test-component-setup";
import Sidebar, { SYNC_SIDEBAR_RESIZER_HEIGHT } from "./Sidebar";
import {
  SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  SYNC_SIDEBAR_DEFAULT_HEIGHT,
} from "./Sidebar/SyncSidebar";

const OBSERVED_AREA_HEIGHT = 600;
const MEASURED_MAX_HEIGHT = OBSERVED_AREA_HEIGHT - SYNC_SIDEBAR_RESIZER_HEIGHT;

const syncSidebarHeight = () =>
  screen.getByTestId("sync-sidebar").style.getPropertyValue("height");

const toggle = () => screen.getByTestId("sync-sidebar-toggle");
const resizer = () => screen.getByTestId("sync-sidebar-resizer");

const dragBy = (delta: number) => {
  fireEvent.mouseDown(resizer(), { button: 0, clientY: 500 });
  fireEvent.mouseMove(window, { clientY: 500 - delta });
  fireEvent.mouseUp(window);
};

const renderSidebar = () =>
  renderWithProviders(<Sidebar focusedPanel="sidebar" />);

const setSyncSidebarFlag = (enabled: boolean) => {
  (globalThis as unknown as { __SYNC_SIDEBAR__: boolean }).__SYNC_SIDEBAR__ =
    enabled;
};

const waitForMeasurement = () =>
  waitFor(() =>
    expect(resizer()).toHaveAttribute(
      "aria-valuemax",
      String(MEASURED_MAX_HEIGHT),
    ),
  );

describe("Sidebar", () => {
  describe("sync sidebar", () => {
    beforeEach(() => {
      setSyncSidebarFlag(true);
    });

    afterEach(() => {
      setSyncSidebarFlag(false);
    });

    it("starts collapsed to its status bar", () => {
      renderSidebar();

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
      expect(screen.getByTestId("sync-sidebar-body")).not.toBeVisible();
    });

    it("pops up to its default height when the status bar is clicked", async () => {
      renderSidebar();

      await userEvent.click(toggle());

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_DEFAULT_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "true");
      expect(screen.getByTestId("sync-sidebar-body")).toBeVisible();
    });

    it("pops up when the handle is dragged upwards", () => {
      renderSidebar();

      dragBy(200);

      expect(syncSidebarHeight()).toBe(
        `${SYNC_SIDEBAR_COLLAPSED_HEIGHT + 200}px`,
      );
      expect(toggle()).toHaveAttribute("aria-expanded", "true");
    });

    it("collapses when the handle is dragged all the way down", () => {
      renderSidebar();

      dragBy(200);
      dragBy(-400);

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
    });

    it("pops back up to the default height, not a previously dragged one", async () => {
      renderSidebar();

      dragBy(150);
      expect(syncSidebarHeight()).toBe(
        `${SYNC_SIDEBAR_COLLAPSED_HEIGHT + 150}px`,
      );

      await userEvent.click(toggle());
      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);

      await userEvent.click(toggle());
      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_DEFAULT_HEIGHT}px`);
    });

    it("expands far enough to cover the source list, leaving only the handle", async () => {
      renderSidebar();
      await waitForMeasurement();

      fireEvent.keyDown(resizer(), { key: "End" });

      expect(syncSidebarHeight()).toBe(`${MEASURED_MAX_HEIGHT}px`);
      expect(MEASURED_MAX_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT).toBe(
        OBSERVED_AREA_HEIGHT,
      );
    });

    it("keeps the collapsed bar's height out of the list, so no source hides under it", () => {
      renderSidebar();

      expect(
        screen
          .getByTestId("source-list-area")
          .style.getPropertyValue("padding-bottom"),
      ).toBe(
        `${SYNC_SIDEBAR_COLLAPSED_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT}px`,
      );
    });

    it("overlays the source list rather than shrinking it when expanded", async () => {
      renderSidebar();
      await waitForMeasurement();

      const reserved = screen
        .getByTestId("source-list-area")
        .style.getPropertyValue("padding-bottom");

      fireEvent.keyDown(resizer(), { key: "End" });

      // The list stays mounted and keeps the same layout box, so its scroll
      // position and search survive a trip through the sync panel.
      expect(screen.getByRole("listbox")).toBeInTheDocument();
      expect(
        screen
          .getByTestId("source-list-area")
          .style.getPropertyValue("padding-bottom"),
      ).toBe(reserved);
      expect(screen.getByTestId("sync-sidebar-overlay")).toContainElement(
        screen.getByTestId("sync-sidebar"),
      );
    });

    it("resizes with the keyboard and collapses at its lower bound", async () => {
      renderSidebar();
      await waitForMeasurement();

      fireEvent.keyDown(resizer(), { key: "End" });
      fireEvent.keyDown(resizer(), { key: "Home" });

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
    });
  });

  describe("sync sidebar feature flag", () => {
    it("does not render the panel when the flag is off", async () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);
      await screen.findByRole("listbox");

      expect(screen.queryByTestId("sync-sidebar-overlay")).toBeNull();
      expect(screen.queryByTestId("sync-sidebar")).toBeNull();
      expect(screen.queryByTestId("sync-sidebar-resizer")).toBeNull();
    });

    it("gives the whole sidebar to the source list when the flag is off", async () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);
      await screen.findByRole("listbox");

      // No collapsed bar to sit above, so no reserved strip at the bottom.
      expect(
        screen
          .getByTestId("source-list-area")
          .style.getPropertyValue("padding-bottom"),
      ).toBe("");
    });
  });
});
