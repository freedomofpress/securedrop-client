import { describe, it, expect, vi, beforeEach } from "vitest";
import { screen, fireEvent } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { useState } from "react";

import { renderWithProviders } from "../../../test-component-setup";
import SyncSidebarResizer, {
  SYNC_SIDEBAR_RESIZE_STEP,
} from "./SyncSidebarResizer";

const MIN_HEIGHT = 48;
const MAX_HEIGHT = 400;
const START_HEIGHT = 200;

// Stateful harness so a drag reports cumulative movement the way the real
// layout does, rather than replaying against a frozen starting height.
function Harness({
  initialHeight = START_HEIGHT,
  onHeightChange,
}: {
  initialHeight?: number;
  onHeightChange?: (height: number) => void;
}) {
  const [height, setHeight] = useState(initialHeight);
  return (
    <>
      <SyncSidebarResizer
        height={height}
        minHeight={MIN_HEIGHT}
        maxHeight={MAX_HEIGHT}
        onHeightChange={(next) => {
          onHeightChange?.(next);
          setHeight(next);
        }}
      />
      <span data-testid="current-height">{height}</span>
    </>
  );
}

const currentHeight = () =>
  Number(screen.getByTestId("current-height").textContent);

describe("SyncSidebarResizer", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe("accessibility", () => {
    it("exposes the splitter as a separator reporting the current height", () => {
      renderWithProviders(<Harness />);

      const separator = screen.getByTestId("sync-sidebar-resizer");
      expect(separator).toHaveAttribute("role", "separator");
      expect(separator).toHaveAttribute("aria-orientation", "horizontal");
      expect(separator).toHaveAttribute("aria-valuenow", String(START_HEIGHT));
      expect(separator).toHaveAttribute("aria-valuemin", String(MIN_HEIGHT));
      expect(separator).toHaveAttribute("aria-valuemax", String(MAX_HEIGHT));
      expect(separator).toHaveAccessibleName("Resize sync activity panel");
    });

    it("is reachable by keyboard", async () => {
      renderWithProviders(<Harness />);

      await userEvent.tab();
      expect(screen.getByTestId("sync-sidebar-resizer")).toHaveFocus();
    });
  });

  describe("keyboard resizing", () => {
    it("grows and shrinks by a fixed step with the arrow keys", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.keyDown(separator, { key: "ArrowUp" });
      expect(currentHeight()).toBe(START_HEIGHT + SYNC_SIDEBAR_RESIZE_STEP);

      fireEvent.keyDown(separator, { key: "ArrowDown" });
      expect(currentHeight()).toBe(START_HEIGHT);
    });

    it("jumps to the bounds with Home and End", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.keyDown(separator, { key: "End" });
      expect(currentHeight()).toBe(MAX_HEIGHT);

      fireEvent.keyDown(separator, { key: "Home" });
      expect(currentHeight()).toBe(MIN_HEIGHT);
    });

    it("ignores keys it does not handle, leaving them to other handlers", () => {
      const onHeightChange = vi.fn();
      renderWithProviders(<Harness onHeightChange={onHeightChange} />);

      fireEvent.keyDown(screen.getByTestId("sync-sidebar-resizer"), {
        key: "a",
      });
      expect(onHeightChange).not.toHaveBeenCalled();
    });
  });

  describe("mouse resizing", () => {
    it("grows the panel as the pointer moves up, from where the drag started", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientY: 500 });
      expect(separator).toHaveAttribute("data-dragging", "true");

      // The panel is anchored to the bottom, so upwards means taller.
      fireEvent.mouseMove(window, { clientY: 450 });
      expect(currentHeight()).toBe(START_HEIGHT + 50);

      // Cumulative, not incremental: total delta is measured from mousedown.
      fireEvent.mouseMove(window, { clientY: 470 });
      expect(currentHeight()).toBe(START_HEIGHT + 30);

      fireEvent.mouseMove(window, { clientY: 530 });
      expect(currentHeight()).toBe(START_HEIGHT - 30);

      fireEvent.mouseUp(window);
      expect(separator).toHaveAttribute("data-dragging", "false");
    });

    it("stops tracking once the drag ends", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientY: 500 });
      fireEvent.mouseUp(window);

      fireEvent.mouseMove(window, { clientY: 300 });
      expect(currentHeight()).toBe(START_HEIGHT);
    });

    it("clamps to the minimum and maximum height", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientY: 500 });
      fireEvent.mouseMove(window, { clientY: -5000 });
      expect(currentHeight()).toBe(MAX_HEIGHT);

      fireEvent.mouseMove(window, { clientY: 5000 });
      expect(currentHeight()).toBe(MIN_HEIGHT);
    });

    it("ignores non-primary buttons", () => {
      const onHeightChange = vi.fn();
      renderWithProviders(<Harness onHeightChange={onHeightChange} />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 2, clientY: 500 });
      expect(separator).toHaveAttribute("data-dragging", "false");

      fireEvent.mouseMove(window, { clientY: 300 });
      expect(onHeightChange).not.toHaveBeenCalled();
    });

    it("suppresses text selection while dragging and restores it after", () => {
      renderWithProviders(<Harness />);
      const separator = screen.getByTestId("sync-sidebar-resizer");

      fireEvent.mouseDown(separator, { button: 0, clientY: 500 });
      expect(document.body.style.userSelect).toBe("none");
      expect(document.body.style.cursor).toBe("row-resize");

      fireEvent.mouseUp(window);
      expect(document.body.style.userSelect).toBe("");
      expect(document.body.style.cursor).toBe("");
    });
  });
});
