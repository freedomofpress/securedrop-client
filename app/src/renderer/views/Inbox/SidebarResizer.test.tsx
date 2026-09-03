import { describe, it, expect, vi, beforeEach, afterAll } from "vitest";
import { screen, fireEvent } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { useState } from "react";

import i18n from "../../i18n";
import { renderWithProviders } from "../../test-component-setup";
import SidebarResizer, {
  SIDEBAR_DEFAULT_WIDTH,
  SIDEBAR_MAX_WIDTH,
  SIDEBAR_MIN_WIDTH,
  SIDEBAR_RESIZE_STEP,
} from "./SidebarResizer";

// Stateful harness so a drag reports cumulative movement the way the real
// layout does, rather than replaying against a frozen starting width.
function Harness({
  initialWidth = SIDEBAR_DEFAULT_WIDTH,
  onWidthChange,
}: {
  initialWidth?: number;
  onWidthChange?: (width: number) => void;
}) {
  const [width, setWidth] = useState(initialWidth);
  return (
    <>
      <SidebarResizer
        width={width}
        onWidthChange={(next) => {
          onWidthChange?.(next);
          setWidth(next);
        }}
      />
      <span data-testid="current-width">{width}</span>
    </>
  );
}

const currentWidth = () =>
  Number(screen.getByTestId("current-width").textContent);

describe("SidebarResizer", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe("accessibility", () => {
    it("exposes the splitter as a separator reporting the current width", () => {
      renderWithProviders(<Harness />);

      const separator = screen.getByTestId("sidebar-resizer");
      expect(separator).toHaveAttribute("role", "separator");
      expect(separator).toHaveAttribute("aria-orientation", "vertical");
      expect(separator).toHaveAttribute(
        "aria-valuenow",
        String(SIDEBAR_DEFAULT_WIDTH),
      );
      expect(separator).toHaveAttribute(
        "aria-valuemin",
        String(SIDEBAR_MIN_WIDTH),
      );
      expect(separator).toHaveAttribute(
        "aria-valuemax",
        String(SIDEBAR_MAX_WIDTH),
      );
      expect(separator).toHaveAccessibleName("Resize sidebar");
    });

    it("is reachable by keyboard", async () => {
      renderWithProviders(<Harness />);

      await userEvent.tab();
      expect(screen.getByTestId("sidebar-resizer")).toHaveFocus();
    });
  });

  describe("keyboard resizing", () => {
    it("narrows and widens by a fixed step with the arrow keys", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.keyDown(separator, { key: "ArrowLeft" });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH - SIDEBAR_RESIZE_STEP);

      fireEvent.keyDown(separator, { key: "ArrowRight" });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH);
    });

    it("jumps to the bounds with Home and End", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.keyDown(separator, { key: "Home" });
      expect(currentWidth()).toBe(SIDEBAR_MIN_WIDTH);

      fireEvent.keyDown(separator, { key: "End" });
      expect(currentWidth()).toBe(SIDEBAR_MAX_WIDTH);
    });

    it("ignores keys it does not handle, leaving them to other handlers", () => {
      const onWidthChange = vi.fn();
      renderWithProviders(<Harness onWidthChange={onWidthChange} />);

      fireEvent.keyDown(screen.getByTestId("sidebar-resizer"), { key: "a" });
      expect(onWidthChange).not.toHaveBeenCalled();
    });
  });

  describe("mouse resizing", () => {
    it("tracks pointer movement from where the drag started", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      expect(separator).toHaveAttribute("data-dragging", "true");

      fireEvent.mouseMove(window, { clientX: 450 });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH + 50);

      // Cumulative, not incremental: total delta is measured from mousedown.
      fireEvent.mouseMove(window, { clientX: 430 });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH + 30);

      fireEvent.mouseUp(window);
      expect(separator).toHaveAttribute("data-dragging", "false");
    });

    it("stops tracking once the drag ends", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      fireEvent.mouseUp(window);

      fireEvent.mouseMove(window, { clientX: 600 });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH);
    });

    it("clamps to the minimum and maximum width", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      fireEvent.mouseMove(window, { clientX: -1000 });
      expect(currentWidth()).toBe(SIDEBAR_MIN_WIDTH);

      fireEvent.mouseMove(window, { clientX: 5000 });
      expect(currentWidth()).toBe(SIDEBAR_MAX_WIDTH);
    });

    it("ignores non-primary buttons", () => {
      const onWidthChange = vi.fn();
      renderWithProviders(<Harness onWidthChange={onWidthChange} />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 2, clientX: 400 });
      expect(separator).toHaveAttribute("data-dragging", "false");

      fireEvent.mouseMove(window, { clientX: 600 });
      expect(onWidthChange).not.toHaveBeenCalled();
    });

    it("suppresses text selection while dragging and restores it after", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      expect(document.body.style.userSelect).toBe("none");
      expect(document.body.style.cursor).toBe("col-resize");

      fireEvent.mouseUp(window);
      expect(document.body.style.userSelect).toBe("");
      expect(document.body.style.cursor).toBe("");
    });
  });

  // In a right-to-left layout the sidebar sits against the right edge of the
  // window and its handle faces left, so every gesture that widens it in LTR
  // has to narrow it here.
  describe("right-to-left layouts", () => {
    beforeEach(async () => {
      await i18n.changeLanguage("ar");
    });

    afterAll(async () => {
      await i18n.changeLanguage("en");
    });

    it("widens the sidebar when the handle is dragged left", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      fireEvent.mouseMove(window, { clientX: 350 });

      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH + 50);
    });

    it("narrows the sidebar when the handle is dragged right", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      fireEvent.mouseMove(window, { clientX: 450 });

      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH - 50);
    });

    it("mirrors the arrow keys, which still move the separator itself", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      // ArrowLeft moves the separator left, which grows the sidebar to its
      // right, so it is the widening key here.
      fireEvent.keyDown(separator, { key: "ArrowLeft" });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH + SIDEBAR_RESIZE_STEP);

      fireEvent.keyDown(separator, { key: "ArrowRight" });
      expect(currentWidth()).toBe(SIDEBAR_DEFAULT_WIDTH);
    });

    it("keeps Home and End meaning narrowest and widest", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.keyDown(separator, { key: "Home" });
      expect(currentWidth()).toBe(SIDEBAR_MIN_WIDTH);

      fireEvent.keyDown(separator, { key: "End" });
      expect(currentWidth()).toBe(SIDEBAR_MAX_WIDTH);
    });

    it("still clamps to the same bounds", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientX: 400 });
      fireEvent.mouseMove(window, { clientX: -1000 });
      expect(currentWidth()).toBe(SIDEBAR_MAX_WIDTH);

      fireEvent.mouseMove(window, { clientX: 5000 });
      expect(currentWidth()).toBe(SIDEBAR_MIN_WIDTH);
    });
  });
});
