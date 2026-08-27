import { screen, fireEvent } from "@testing-library/react";
import { expect, describe, it } from "vitest";
import InboxView from "./Inbox";
import { renderWithProviders } from "../test-component-setup";
import {
  SIDEBAR_DEFAULT_WIDTH,
  SIDEBAR_MAX_WIDTH,
  SIDEBAR_MIN_WIDTH,
  SIDEBAR_RESIZE_STEP,
} from "./Inbox/SidebarResizer";

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
  });
});
