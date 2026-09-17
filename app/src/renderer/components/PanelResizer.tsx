/*
 * Panel resizing is implemented with a focusable `separator` per the ARIA
 * window splitter pattern. The role is interactive because it is focusable,
 * and adjustable via both mouse and keyboard handlers.
 */
/* eslint-disable jsx-a11y/no-noninteractive-element-interactions */
/* eslint-disable jsx-a11y/no-noninteractive-tabindex */
import { memo, useEffect, useState } from "react";
import type { KeyboardEvent, MouseEvent } from "react";

const DIRECTIONS = {
  right: {
    coordinate: "clientX",
    sign: 1,
    grow: "ArrowRight",
    shrink: "ArrowLeft",
    ariaOrientation: "vertical",
    cursor: "col-resize",
    className: "w-1 cursor-col-resize after:inset-y-0 after:-inset-x-1",
  },
  left: {
    coordinate: "clientX",
    sign: -1,
    grow: "ArrowLeft",
    shrink: "ArrowRight",
    ariaOrientation: "vertical",
    cursor: "col-resize",
    className: "w-1 cursor-col-resize after:inset-y-0 after:-inset-x-1",
  },
  up: {
    coordinate: "clientY",
    sign: -1,
    grow: "ArrowUp",
    shrink: "ArrowDown",
    ariaOrientation: "horizontal",
    cursor: "row-resize",
    className: "h-1 cursor-row-resize after:inset-x-0 after:-inset-y-1",
  },
} as const;

export type ResizeDirection = keyof typeof DIRECTIONS;

const clamp = (size: number, minSize: number, maxSize: number) =>
  Math.min(maxSize, Math.max(minSize, size));

interface PanelResizerProps {
  growsToward: ResizeDirection;
  size: number;
  minSize: number;
  maxSize: number;
  // Pixels per arrow-key press when the handle has keyboard focus.
  step: number;
  label: string;
  hint: string;
  testId: string;
  onSizeChange: (size: number) => void;
}

const PanelResizer = memo(function PanelResizer({
  growsToward,
  size,
  minSize,
  maxSize,
  step,
  label,
  hint,
  testId,
  onSizeChange,
}: PanelResizerProps) {
  const direction = DIRECTIONS[growsToward];

  const [drag, setDrag] = useState<{ origin: number; size: number } | null>(
    null,
  );

  useEffect(() => {
    if (!drag) {
      return;
    }

    const handleMouseMove = (e: globalThis.MouseEvent) => {
      const delta = e[direction.coordinate] - drag.origin;
      onSizeChange(clamp(drag.size + direction.sign * delta, minSize, maxSize));
    };
    const handleMouseUp = () => setDrag(null);

    window.addEventListener("mousemove", handleMouseMove);
    window.addEventListener("mouseup", handleMouseUp);

    document.body.style.userSelect = "none";
    document.body.style.cursor = direction.cursor;

    return () => {
      window.removeEventListener("mousemove", handleMouseMove);
      window.removeEventListener("mouseup", handleMouseUp);
      document.body.style.userSelect = "";
      document.body.style.cursor = "";
    };
  }, [drag, direction, minSize, maxSize, onSizeChange]);

  const handleMouseDown = (e: MouseEvent<HTMLDivElement>) => {
    if (e.button !== 0) {
      return;
    }
    e.preventDefault();
    setDrag({ origin: e[direction.coordinate], size });
  };

  const handleKeyDown = (e: KeyboardEvent<HTMLDivElement>) => {
    const bindings: Record<string, number | undefined> = {
      [direction.grow]: size + step,
      [direction.shrink]: size - step,
      Home: minSize,
      End: maxSize,
    };
    const next = bindings[e.key];
    if (next === undefined) {
      return;
    }
    onSizeChange(clamp(next, minSize, maxSize));
    e.preventDefault();
  };

  return (
    <div
      role="separator"
      aria-orientation={direction.ariaOrientation}
      aria-label={label}
      aria-valuenow={size}
      aria-valuemin={minSize}
      aria-valuemax={maxSize}
      tabIndex={0}
      title={hint}
      data-testid={testId}
      data-dragging={drag !== null}
      onMouseDown={handleMouseDown}
      onKeyDown={handleKeyDown}
      className={`relative flex-shrink-0 outline-0 transition-colors duration-150 after:absolute after:content-[''] focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2 ${direction.className} ${
        drag ? "bg-blue-400" : "bg-transparent hover:bg-blue-200"
      }`}
    />
  );
});

export default PanelResizer;
