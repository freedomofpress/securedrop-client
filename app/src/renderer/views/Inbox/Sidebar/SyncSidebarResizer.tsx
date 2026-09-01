/* eslint-disable jsx-a11y/no-noninteractive-element-interactions */
/* eslint-disable jsx-a11y/no-noninteractive-tabindex */
/* eslint-disable react-refresh/only-export-components */
import { memo, useEffect, useState } from "react";
import type { KeyboardEvent, MouseEvent } from "react";
import { useTranslation } from "react-i18next";

export const SYNC_SIDEBAR_RESIZER_HEIGHT = 4;

export const SYNC_SIDEBAR_RESIZE_STEP = 16;

const clamp = (height: number, minHeight: number, maxHeight: number) =>
  Math.min(maxHeight, Math.max(minHeight, height));

interface SyncSidebarResizerProps {
  height: number;
  minHeight: number;
  maxHeight: number;
  onHeightChange: (height: number) => void;
}

/*
 * Sync sidebar resizer is implemented with a focusable `separator` per the
 * ARIA window splitter pattern. The role is interactive because it is
 * focusable, and adjustable via both mouse and keyboard handlers.
 */
const SyncSidebarResizer = memo(function SyncSidebarResizer({
  height,
  minHeight,
  maxHeight,
  onHeightChange,
}: SyncSidebarResizerProps) {
  const { t } = useTranslation("Sidebar");

  const [drag, setDrag] = useState<{ y: number; height: number } | null>(null);

  useEffect(() => {
    if (!drag) {
      return;
    }

    const handleMouseMove = (e: globalThis.MouseEvent) =>
      onHeightChange(
        clamp(drag.height + (drag.y - e.clientY), minHeight, maxHeight),
      );
    const handleMouseUp = () => setDrag(null);

    window.addEventListener("mousemove", handleMouseMove);
    window.addEventListener("mouseup", handleMouseUp);

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
    if (e.button !== 0) {
      return;
    }
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
      className={`relative h-1 flex-shrink-0 cursor-row-resize outline-0 transition-colors duration-150 after:absolute after:inset-x-0 after:-inset-y-1 after:content-[''] focus-visible:outline-2 focus-visible:outline-blue-300 focus-visible:-outline-offset-2 ${
        drag ? "bg-blue-400" : "bg-transparent hover:bg-blue-200"
      }`}
    />
  );
});

export default SyncSidebarResizer;
