import {
  screen,
  fireEvent,
  cleanup,
  act,
  waitFor,
} from "@testing-library/react";
import { expect, describe, it, beforeEach, afterEach, vi } from "vitest";
import { renderWithProviders } from "../test-component-setup";
import i18n from "../i18n";
import { PSEUDO_RTL_LANGUAGE } from "../locales";
import InboxView, {
  SIDEBAR_DEFAULT_WIDTH,
  SIDEBAR_MAX_WIDTH,
  SIDEBAR_MIN_WIDTH,
  SIDEBAR_RESIZE_STEP,
} from "./Inbox";

const sidebarWidth = () =>
  screen.getByTestId("sidebar-panel").style.getPropertyValue("width");

// Drag the resize handle by `delta` pixels, starting from an arbitrary but
// consistent pointer position.
const dragBy = (delta: number) => {
  const separator = screen.getByTestId("sidebar-resizer");
  fireEvent.mouseDown(separator, { button: 0, clientX: 500 });
  fireEvent.mouseMove(window, { clientX: 500 + delta });
  fireEvent.mouseUp(window);
};

describe("InboxView Component", () => {
  it('says the string "Select a source"', () => {
    renderWithProviders(<InboxView />);
    expect(screen.getByText("Select a source")).toBeInTheDocument();
  });

  describe("resizable sidebar", () => {
    it("starts at the default width", () => {
      renderWithProviders(<InboxView />);
      expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH}px`);
    });

    it("widens and narrows when the handle is dragged", () => {
      renderWithProviders(<InboxView />);

      dragBy(60);
      expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH + 60}px`);

      dragBy(-100);
      expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH - 40}px`);
    });

    it("resizes with the keyboard and stays within its bounds", () => {
      renderWithProviders(<InboxView />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.keyDown(separator, { key: "ArrowRight" });
      expect(sidebarWidth()).toBe(
        `${SIDEBAR_DEFAULT_WIDTH + SIDEBAR_RESIZE_STEP}px`,
      );

      fireEvent.keyDown(separator, { key: "Home" });
      expect(sidebarWidth()).toBe(`${SIDEBAR_MIN_WIDTH}px`);

      fireEvent.keyDown(separator, { key: "End" });
      expect(sidebarWidth()).toBe(`${SIDEBAR_MAX_WIDTH}px`);
    });

    describe("in a right-to-left locale", () => {
      beforeEach(async () => {
        await i18n.changeLanguage(PSEUDO_RTL_LANGUAGE);
      });

      afterEach(async () => {
        // Unmount before restoring the language, so nothing re-renders
        // outside act() when the locale changes back.
        cleanup();
        await i18n.changeLanguage("en");
      });

      // The sidebar is on the trailing side of a mirrored layout, so the
      // handle has to move the other way to widen it.
      it("narrows the sidebar when the handle is dragged to the right", () => {
        renderWithProviders(<InboxView />);

        dragBy(60);
        expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH - 60}px`);

        dragBy(-100);
        expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH + 40}px`);
      });

      it("widens with ArrowLeft rather than ArrowRight", () => {
        renderWithProviders(<InboxView />);
        const separator = screen.getByTestId("sidebar-resizer");

        fireEvent.keyDown(separator, { key: "ArrowLeft" });
        expect(sidebarWidth()).toBe(
          `${SIDEBAR_DEFAULT_WIDTH + SIDEBAR_RESIZE_STEP}px`,
        );

        fireEvent.keyDown(separator, { key: "ArrowRight" });
        expect(sidebarWidth()).toBe(`${SIDEBAR_DEFAULT_WIDTH}px`);
      });
    });
  });

  describe("sync activity", () => {
    it("re-reads the activity snapshot when a pending event is written", async () => {
      renderWithProviders(<InboxView />);
      const api = window.electronAPI;

      await waitFor(() => expect(api.getSyncActivity).toHaveBeenCalledTimes(1));

      // A write in the main process announces itself; without this the queue
      // would stay invisible until the next sync finished.
      const notify = vi.mocked(api.onPendingEventsChanged).mock.calls[0][0];
      await act(async () => notify());

      await waitFor(() => expect(api.getSyncActivity).toHaveBeenCalledTimes(2));
    });

    it("stops listening once the inbox goes away", () => {
      const unsubscribe = vi.fn();
      vi.mocked(window.electronAPI.onPendingEventsChanged).mockReturnValue(
        unsubscribe,
      );

      const { unmount } = renderWithProviders(<InboxView />);
      unmount();

      expect(unsubscribe).toHaveBeenCalled();
    });
  });
});
