import { describe, it, expect, vi } from "vitest";
import { fireEvent, renderHook } from "@testing-library/react";
import { useSidebarShortcuts } from "./useSidebarShortcuts";

describe("useSidebarShortcuts", () => {
  const createHandlers = (enabled: boolean) => ({
    onSourceUp: vi.fn(),
    onSourceDown: vi.fn(),
    onSourceSelect: vi.fn(),
    onDeleteCheckedSources: vi.fn(),
    enabled,
  });

  it("fires onSourceUp on Up arrow when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: "ArrowUp", code: "ArrowUp" });

    expect(handlers.onSourceUp).toHaveBeenCalledTimes(1);
  });

  it("fires onSourceDown on Down arrow when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: "ArrowDown", code: "ArrowDown" });

    expect(handlers.onSourceDown).toHaveBeenCalledTimes(1);
  });

  it("fires onSourceSelect on Enter when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: "Enter", code: "Enter" });

    expect(handlers.onSourceSelect).toHaveBeenCalledTimes(1);
  });

  it("fires onSourceSelect on Space when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: " ", code: "Space" });

    expect(handlers.onSourceSelect).toHaveBeenCalledTimes(1);
  });

  it("fires onDeleteCheckedSources on Delete when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: "Delete", code: "Delete" });

    expect(handlers.onDeleteCheckedSources).toHaveBeenCalledTimes(1);
  });

  it("does NOT fire any handler when disabled", () => {
    const handlers = createHandlers(false);
    renderHook(() => useSidebarShortcuts(handlers));

    fireEvent.keyDown(document, { key: "ArrowUp", code: "ArrowUp" });
    fireEvent.keyDown(document, { key: "ArrowDown", code: "ArrowDown" });
    fireEvent.keyDown(document, { key: "Enter", code: "Enter" });
    fireEvent.keyDown(document, { key: " ", code: "Space" });
    fireEvent.keyDown(document, { key: "Delete", code: "Delete" });

    expect(handlers.onSourceUp).not.toHaveBeenCalled();
    expect(handlers.onSourceDown).not.toHaveBeenCalled();
    expect(handlers.onSourceSelect).not.toHaveBeenCalled();
    expect(handlers.onDeleteCheckedSources).not.toHaveBeenCalled();
  });

  it("respects enabled toggle via rerender", () => {
    const handlers = createHandlers(false);
    const { rerender } = renderHook((props) => useSidebarShortcuts(props), {
      initialProps: handlers,
    });

    fireEvent.keyDown(document, { key: "ArrowUp", code: "ArrowUp" });
    expect(handlers.onSourceUp).not.toHaveBeenCalled();

    // Enable
    rerender({ ...handlers, enabled: true });

    fireEvent.keyDown(document, { key: "ArrowUp", code: "ArrowUp" });
    expect(handlers.onSourceUp).toHaveBeenCalledTimes(1);
  });
});
