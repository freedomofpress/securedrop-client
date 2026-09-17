import { describe, it, expect, vi, beforeEach } from "vitest";
import { screen, fireEvent } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { useState } from "react";

import { renderWithProviders } from "../test-component-setup";
import PanelResizer, { type ResizeDirection } from "./PanelResizer";

const MIN_SIZE = 48;
const MAX_SIZE = 400;
const START_SIZE = 200;
const STEP = 16;
const LABEL = "Resize panel";
const HINT = "Drag or use the arrow keys";

// Where the pointer starts every drag; arbitrary, but well inside the bounds.
const ORIGIN = 500;

// Stateful harness so a drag reports cumulative movement the way the real
// layout does, rather than replaying against a frozen starting size.
function Harness({
  growsToward,
  initialSize = START_SIZE,
  onSizeChange,
}: {
  growsToward: ResizeDirection;
  initialSize?: number;
  onSizeChange?: (size: number) => void;
}) {
  const [size, setSize] = useState(initialSize);
  return (
    <>
      <PanelResizer
        growsToward={growsToward}
        size={size}
        minSize={MIN_SIZE}
        maxSize={MAX_SIZE}
        step={STEP}
        label={LABEL}
        hint={HINT}
        testId="panel-resizer"
        onSizeChange={(next) => {
          onSizeChange?.(next);
          setSize(next);
        }}
      />
      <span data-testid="current-size">{size}</span>
    </>
  );
}

const separator = () => screen.getByTestId("panel-resizer");

const currentSize = () =>
  Number(screen.getByTestId("current-size").textContent);

interface DirectionCase {
  growsToward: ResizeDirection;
  // Pointer axis the direction reads, and which way it has to travel to grow.
  coordinate: "clientX" | "clientY";
  sign: 1 | -1;
  ariaOrientation: string;
  cursor: string;
  growKey: string;
  shrinkKey: string;
}

const DIRECTION_CASES: DirectionCase[] = [
  {
    growsToward: "right",
    coordinate: "clientX",
    sign: 1,
    ariaOrientation: "vertical",
    cursor: "col-resize",
    growKey: "ArrowRight",
    shrinkKey: "ArrowLeft",
  },
  {
    growsToward: "left",
    coordinate: "clientX",
    sign: -1,
    ariaOrientation: "vertical",
    cursor: "col-resize",
    growKey: "ArrowLeft",
    shrinkKey: "ArrowRight",
  },
  {
    growsToward: "up",
    coordinate: "clientY",
    sign: -1,
    ariaOrientation: "horizontal",
    cursor: "row-resize",
    growKey: "ArrowUp",
    shrinkKey: "ArrowDown",
  },
];

describe.each(DIRECTION_CASES)(
  "PanelResizer growing toward $growsToward",
  ({
    growsToward,
    coordinate,
    sign,
    ariaOrientation,
    cursor,
    growKey,
    shrinkKey,
  }) => {
    // Pointer position that asks the panel to grow by `delta` pixels, in
    // whichever direction this panel grows.
    const pointerAt = (delta: number) => ({
      [coordinate]: ORIGIN + sign * delta,
    });

    const startDrag = () =>
      fireEvent.mouseDown(separator(), { button: 0, ...pointerAt(0) });

    const moveTo = (delta: number) =>
      fireEvent.mouseMove(window, pointerAt(delta));

    beforeEach(() => {
      vi.clearAllMocks();
    });

    describe("accessibility", () => {
      it("exposes the splitter as a separator reporting the current size", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        expect(separator()).toHaveAttribute("role", "separator");
        expect(separator()).toHaveAttribute(
          "aria-orientation",
          ariaOrientation,
        );
        expect(separator()).toHaveAttribute(
          "aria-valuenow",
          String(START_SIZE),
        );
        expect(separator()).toHaveAttribute("aria-valuemin", String(MIN_SIZE));
        expect(separator()).toHaveAttribute("aria-valuemax", String(MAX_SIZE));
        expect(separator()).toHaveAccessibleName(LABEL);
      });

      it("is reachable by keyboard", async () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        await userEvent.tab();
        expect(separator()).toHaveFocus();
      });
    });

    describe("keyboard resizing", () => {
      it("grows and shrinks by a fixed step with the arrow keys", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        fireEvent.keyDown(separator(), { key: growKey });
        expect(currentSize()).toBe(START_SIZE + STEP);

        fireEvent.keyDown(separator(), { key: shrinkKey });
        expect(currentSize()).toBe(START_SIZE);
      });

      it("jumps to the bounds with Home and End", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        fireEvent.keyDown(separator(), { key: "End" });
        expect(currentSize()).toBe(MAX_SIZE);

        fireEvent.keyDown(separator(), { key: "Home" });
        expect(currentSize()).toBe(MIN_SIZE);
      });

      it("ignores keys it does not handle, leaving them to other handlers", () => {
        const onSizeChange = vi.fn();
        renderWithProviders(
          <Harness growsToward={growsToward} onSizeChange={onSizeChange} />,
        );

        fireEvent.keyDown(separator(), { key: "a" });
        expect(onSizeChange).not.toHaveBeenCalled();
      });
    });

    describe("mouse resizing", () => {
      it("tracks pointer movement from where the drag started", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        startDrag();
        expect(separator()).toHaveAttribute("data-dragging", "true");

        moveTo(50);
        expect(currentSize()).toBe(START_SIZE + 50);

        // Cumulative, not incremental: total delta is measured from mousedown.
        moveTo(30);
        expect(currentSize()).toBe(START_SIZE + 30);

        moveTo(-30);
        expect(currentSize()).toBe(START_SIZE - 30);

        fireEvent.mouseUp(window);
        expect(separator()).toHaveAttribute("data-dragging", "false");
      });

      it("stops tracking once the drag ends", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        startDrag();
        fireEvent.mouseUp(window);

        moveTo(100);
        expect(currentSize()).toBe(START_SIZE);
      });

      it("clamps to the minimum and maximum size", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        startDrag();
        moveTo(5000);
        expect(currentSize()).toBe(MAX_SIZE);

        moveTo(-5000);
        expect(currentSize()).toBe(MIN_SIZE);
      });

      it("ignores non-primary buttons", () => {
        const onSizeChange = vi.fn();
        renderWithProviders(
          <Harness growsToward={growsToward} onSizeChange={onSizeChange} />,
        );

        fireEvent.mouseDown(separator(), { button: 2, ...pointerAt(0) });
        expect(separator()).toHaveAttribute("data-dragging", "false");

        moveTo(100);
        expect(onSizeChange).not.toHaveBeenCalled();
      });

      it("suppresses text selection while dragging and restores it after", () => {
        renderWithProviders(<Harness growsToward={growsToward} />);

        startDrag();
        expect(document.body.style.userSelect).toBe("none");
        expect(document.body.style.cursor).toBe(cursor);

        fireEvent.mouseUp(window);
        expect(document.body.style.userSelect).toBe("");
        expect(document.body.style.cursor).toBe("");
      });
    });
  },
);
