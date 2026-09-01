/*
 * Sidebar resizing is implemented with a focusable `separator` per the ARIA
 * window splitter pattern. The role is interactive because it is focusable,
 * and adjustable via both mouse and keyboard handlers.
 */
/* eslint-disable jsx-a11y/no-noninteractive-element-interactions */
/* eslint-disable jsx-a11y/no-noninteractive-tabindex */
/* eslint-disable react-refresh/only-export-components */
import { memo, useEffect, useState } from "react";
import type { KeyboardEvent, MouseEvent } from "react";
import { useTranslation } from "react-i18next";

export const SIDEBAR_DEFAULT_WIDTH = 384;

export const SIDEBAR_MIN_WIDTH = 260;

export const SIDEBAR_MAX_WIDTH = 640;

// Pixels per arrow-key press when the resize handle has keyboard focus.
export const SIDEBAR_RESIZE_STEP = 16;

const clamp = (width: number) =>
  Math.min(SIDEBAR_MAX_WIDTH, Math.max(SIDEBAR_MIN_WIDTH, width));

interface SidebarResizerProps {
  width: number;
  onWidthChange: (width: number) => void;
}

/**
 * Drag handle between the sidebar and the main content.
 *
 * Implements the ARIA window splitter pattern: a focusable `role="separator"`
 * that reports the current width, so the sidebar can be resized with the arrow
 * keys as well as the mouse.
 */
const SidebarResizer = memo(function SidebarResizer({
  width,
  onWidthChange,
}: SidebarResizerProps) {
  const { t } = useTranslation("Sidebar");

  // Pointer position and sidebar width at mousedown; null when not dragging.
  // Tracking the delta rather than the absolute pointer position keeps the
  // handle from jumping when the grab point isn't exactly on the divider.
  const [drag, setDrag] = useState<{ x: number; width: number } | null>(null);

  useEffect(() => {
    if (!drag) {
      return;
    }

    // Listen on the window, not the handle: the pointer routinely outruns a
    // few-pixel-wide divider mid-drag, and the drag must continue anyway.
    const handleMouseMove = (e: globalThis.MouseEvent) =>
      onWidthChange(clamp(drag.width + (e.clientX - drag.x)));
    const handleMouseUp = () => setDrag(null);

    window.addEventListener("mousemove", handleMouseMove);
    window.addEventListener("mouseup", handleMouseUp);

    // Keep the resize cursor and suppress selection across the whole window
    // for the duration of the drag, wherever the pointer ends up.
    document.body.style.userSelect = "none";
    document.body.style.cursor = "col-resize";

    return () => {
      window.removeEventListener("mousemove", handleMouseMove);
      window.removeEventListener("mouseup", handleMouseUp);
      document.body.style.userSelect = "";
      document.body.style.cursor = "";
    };
  }, [drag, onWidthChange]);

  const handleMouseDown = (e: MouseEvent<HTMLDivElement>) => {
    // Primary button only; ignore middle/right clicks and context menus.
    if (e.button !== 0) {
      return;
    }
    // Suppress the text selection that a drag across the panels would start.
    e.preventDefault();
    setDrag({ x: e.clientX, width });
  };

  const handleKeyDown = (e: KeyboardEvent<HTMLDivElement>) => {
    const next = {
      ArrowLeft: width - SIDEBAR_RESIZE_STEP,
      ArrowRight: width + SIDEBAR_RESIZE_STEP,
      Home: SIDEBAR_MIN_WIDTH,
      End: SIDEBAR_MAX_WIDTH,
    }[e.key];
    // Only swallow the keys we actually handled, so the sidebar's own
    // shortcuts keep working when the handle happens to hold focus.
    if (next === undefined) {
      return;
    }
    onWidthChange(clamp(next));
    e.preventDefault();
  };

  return (
    <div
      role="separator"
      aria-orientation="vertical"
      aria-label={t("resizer.label")}
      aria-valuenow={width}
      aria-valuemin={SIDEBAR_MIN_WIDTH}
      aria-valuemax={SIDEBAR_MAX_WIDTH}
      tabIndex={0}
      title={t("resizer.hint")}
      data-testid="sidebar-resizer"
      data-dragging={drag !== null}
      onMouseDown={handleMouseDown}
      onKeyDown={handleKeyDown}
      // The `after` pseudo-element widens the grab area past the visible
      // divider without taking up any layout space, so the handle is
      // comfortable to hit with a mouse.
      className={`relative w-1 flex-shrink-0 cursor-col-resize outline-0 transition-colors duration-150 after:absolute after:inset-y-0 after:-inset-x-1 after:content-[''] focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2 ${
        drag ? "bg-blue-400" : "bg-transparent hover:bg-blue-200"
      }`}
    />
  );
});

export default SidebarResizer;
