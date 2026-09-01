/*
 * Sync sidebar resizing is implemented with a focusable `separator` per the
 * ARIA window splitter pattern. The role is interactive because it is
 * focusable, and adjustable via both mouse and keyboard handlers.
 */
/* eslint-disable jsx-a11y/no-noninteractive-element-interactions */
/* eslint-disable jsx-a11y/no-noninteractive-tabindex */
/* eslint-disable react-refresh/only-export-components */
import { memo, useEffect, useState } from "react";
import type { KeyboardEvent, MouseEvent } from "react";
import { useTranslation } from "react-i18next";

// Thickness of the handle, which stays visible above a fully expanded panel so
// it can always be grabbed again. Keep in sync with the `h-1` class below.
export const SYNC_SIDEBAR_RESIZER_HEIGHT = 4;

// Pixels per arrow-key press when the resize handle has keyboard focus.
export const SYNC_SIDEBAR_RESIZE_STEP = 16;

const clamp = (height: number, minHeight: number, maxHeight: number) =>
  Math.min(maxHeight, Math.max(minHeight, height));

interface SyncSidebarResizerProps {
  height: number;
  minHeight: number;
  maxHeight: number;
  onHeightChange: (height: number) => void;
}

/**
 * Drag handle along the top edge of the sync sidebar.
 *
 * Implements the ARIA window splitter pattern: a focusable `role="separator"`
 * that reports the current height, so the panel can be resized with the arrow
 * keys as well as the mouse. Dragging all the way down collapses the panel,
 * which is what makes it poppable open from its collapsed position without
 * having to reach for the header's toggle.
 */
const SyncSidebarResizer = memo(function SyncSidebarResizer({
  height,
  minHeight,
  maxHeight,
  onHeightChange,
}: SyncSidebarResizerProps) {
  const { t } = useTranslation("Sidebar");

  // Pointer position and panel height at mousedown; null when not dragging.
  // Tracking the delta rather than the absolute pointer position keeps the
  // handle from jumping when the grab point isn't exactly on the divider.
  const [drag, setDrag] = useState<{ y: number; height: number } | null>(null);

  useEffect(() => {
    if (!drag) {
      return;
    }

    // Listen on the window, not the handle: the pointer routinely outruns a
    // few-pixel-tall divider mid-drag, and the drag must continue anyway.
    // The panel grows upwards, so a decreasing clientY means a taller panel.
    const handleMouseMove = (e: globalThis.MouseEvent) =>
      onHeightChange(
        clamp(drag.height + (drag.y - e.clientY), minHeight, maxHeight),
      );
    const handleMouseUp = () => setDrag(null);

    window.addEventListener("mousemove", handleMouseMove);
    window.addEventListener("mouseup", handleMouseUp);

    // Keep the resize cursor and suppress selection across the whole window
    // for the duration of the drag, wherever the pointer ends up.
    document.body.style.userSelect = "none";
    document.body.style.cursor = "row-resize";

    return () => {
      window.removeEventListener("mousemove", handleMouseMove);
      window.removeEventListener("mouseup", handleMouseUp);
      document.body.style.userSelect = "";
      document.body.style.cursor = "";
    };
  }, [drag, onHeightChange, minHeight, maxHeight]);

  const handleMouseDown = (e: MouseEvent<HTMLDivElement>) => {
    // Primary button only; ignore middle/right clicks and context menus.
    if (e.button !== 0) {
      return;
    }
    // Suppress the text selection that a drag across the panels would start.
    e.preventDefault();
    setDrag({ y: e.clientY, height });
  };

  const handleKeyDown = (e: KeyboardEvent<HTMLDivElement>) => {
    const next = {
      ArrowUp: height + SYNC_SIDEBAR_RESIZE_STEP,
      ArrowDown: height - SYNC_SIDEBAR_RESIZE_STEP,
      Home: minHeight,
      End: maxHeight,
    }[e.key];
    // Only swallow the keys we actually handled, so the sidebar's own
    // shortcuts keep working when the handle happens to hold focus.
    if (next === undefined) {
      return;
    }
    onHeightChange(clamp(next, minHeight, maxHeight));
    e.preventDefault();
  };

  return (
    <div
      role="separator"
      aria-orientation="horizontal"
      aria-label={t("syncSidebar.resizer.label")}
      aria-valuenow={height}
      aria-valuemin={minHeight}
      aria-valuemax={maxHeight}
      tabIndex={0}
      title={t("syncSidebar.resizer.hint")}
      data-testid="sync-sidebar-resizer"
      data-dragging={drag !== null}
      onMouseDown={handleMouseDown}
      onKeyDown={handleKeyDown}
      // The `after` pseudo-element widens the grab area past the visible
      // divider without taking up any layout space, so the handle is
      // comfortable to hit with a mouse.
      className={`relative h-1 flex-shrink-0 cursor-row-resize outline-0 transition-colors duration-150 after:absolute after:inset-x-0 after:-inset-y-1 after:content-[''] focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2 ${
        drag ? "bg-blue-400" : "bg-transparent hover:bg-blue-200"
      }`}
    />
  );
});

export default SyncSidebarResizer;
