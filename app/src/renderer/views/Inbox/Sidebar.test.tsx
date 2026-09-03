import { describe, it, expect } from "vitest";
import { screen, fireEvent, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";

import { renderWithProviders } from "../../test-component-setup";
import Sidebar from "./Sidebar";
import {
  SYNC_SIDEBAR_COLLAPSED_HEIGHT,
  SYNC_SIDEBAR_DEFAULT_HEIGHT,
} from "./Sidebar/SyncSidebar";
import { SYNC_SIDEBAR_RESIZER_HEIGHT } from "./Sidebar/SyncSidebarResizer";

// The ResizeObserver stub in test-component-setup reports this height for
// every observed element, including the area the panel overlays.
const OBSERVED_AREA_HEIGHT = 600;
const MEASURED_MAX_HEIGHT = OBSERVED_AREA_HEIGHT - SYNC_SIDEBAR_RESIZER_HEIGHT;

const syncSidebarHeight = () =>
  screen.getByTestId("sync-sidebar").style.getPropertyValue("height");

const toggle = () => screen.getByTestId("sync-sidebar-toggle");
const resizer = () => screen.getByTestId("sync-sidebar-resizer");

// Drag the resize handle by `delta` pixels, positive meaning upwards (taller),
// from an arbitrary but consistent pointer position.
const dragBy = (delta: number) => {
  fireEvent.mouseDown(resizer(), { button: 0, clientY: 500 });
  fireEvent.mouseMove(window, { clientY: 500 - delta });
  fireEvent.mouseUp(window);
};

// The sidebar's height is only known once the ResizeObserver stub has fired,
// which it does on the next macrotask.
const waitForMeasurement = () =>
  waitFor(() =>
    expect(resizer()).toHaveAttribute(
      "aria-valuemax",
      String(MEASURED_MAX_HEIGHT),
    ),
  );

describe("Sidebar", () => {
  describe("sync sidebar", () => {
    it("starts collapsed to its status bar", () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
      expect(screen.getByTestId("sync-sidebar-body")).not.toBeVisible();
    });

    it("pops up to its default height when the status bar is clicked", async () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

      await userEvent.click(toggle());

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_DEFAULT_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "true");
      expect(screen.getByTestId("sync-sidebar-body")).toBeVisible();
    });

    it("pops up when the handle is dragged upwards", () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

      dragBy(200);

      expect(syncSidebarHeight()).toBe(
        `${SYNC_SIDEBAR_COLLAPSED_HEIGHT + 200}px`,
      );
      expect(toggle()).toHaveAttribute("aria-expanded", "true");
    });

    it("collapses when the handle is dragged all the way down", () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

      dragBy(200);
      dragBy(-400);

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
    });

    it("pops back up to the default height, not a previously dragged one", async () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

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
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);
      await waitForMeasurement();

      fireEvent.keyDown(resizer(), { key: "End" });

      expect(syncSidebarHeight()).toBe(`${MEASURED_MAX_HEIGHT}px`);
      expect(MEASURED_MAX_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT).toBe(
        OBSERVED_AREA_HEIGHT,
      );
    });

    it("keeps the collapsed bar's height out of the list, so no source hides under it", () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);

      expect(
        screen
          .getByTestId("source-list-area")
          .style.getPropertyValue("padding-bottom"),
      ).toBe(
        `${SYNC_SIDEBAR_COLLAPSED_HEIGHT + SYNC_SIDEBAR_RESIZER_HEIGHT}px`,
      );
    });

    it("overlays the source list rather than shrinking it when expanded", async () => {
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);
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
      renderWithProviders(<Sidebar focusedPanel="sidebar" />);
      await waitForMeasurement();

      fireEvent.keyDown(resizer(), { key: "End" });
      fireEvent.keyDown(resizer(), { key: "Home" });

      expect(syncSidebarHeight()).toBe(`${SYNC_SIDEBAR_COLLAPSED_HEIGHT}px`);
      expect(toggle()).toHaveAttribute("aria-expanded", "false");
    });
  });
});
