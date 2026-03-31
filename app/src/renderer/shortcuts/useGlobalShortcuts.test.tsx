import { describe, it, expect, vi } from "vitest";
import { fireEvent, renderHook } from "@testing-library/react";
import { useGlobalShortcuts } from "./useGlobalShortcuts";

describe("useGlobalShortcuts", () => {
  const createHandlers = () => ({
    onQuit: vi.fn(),
    onFocusSidebar: vi.fn(),
    onFocusMainContent: vi.fn(),
    onOpenHelp: vi.fn(),
    onSync: vi.fn(),
    onSignOut: vi.fn(),
  });

  it("fires onQuit on Ctrl+Q", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(handlers.onQuit).toHaveBeenCalledTimes(1);
  });

  it("fires onFocusSidebar on Left arrow", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "ArrowLeft", code: "ArrowLeft" });

    expect(handlers.onFocusSidebar).toHaveBeenCalledTimes(1);
  });

  it("fires onFocusMainContent on Right arrow", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "ArrowRight", code: "ArrowRight" });

    expect(handlers.onFocusMainContent).toHaveBeenCalledTimes(1);
  });

  it("fires onOpenHelp on F1", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "F1", code: "F1" });

    expect(handlers.onOpenHelp).toHaveBeenCalledTimes(1);
  });

  it("fires onSync on Ctrl+S", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "s", code: "KeyS", ctrlKey: true });

    expect(handlers.onSync).toHaveBeenCalledTimes(1);
  });

  it("fires onSignOut on Ctrl+Shift+O", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, {
      key: "o",
      code: "KeyO",
      ctrlKey: true,
      shiftKey: true,
    });

    expect(handlers.onSignOut).toHaveBeenCalledTimes(1);
  });

  it("does not fire other handlers when one shortcut is pressed", () => {
    const handlers = createHandlers();
    renderHook(() => useGlobalShortcuts(handlers));

    fireEvent.keyDown(document, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(handlers.onQuit).toHaveBeenCalledTimes(1);
    expect(handlers.onFocusSidebar).not.toHaveBeenCalled();
    expect(handlers.onFocusMainContent).not.toHaveBeenCalled();
    expect(handlers.onOpenHelp).not.toHaveBeenCalled();
    expect(handlers.onSync).not.toHaveBeenCalled();
    expect(handlers.onSignOut).not.toHaveBeenCalled();
  });
});
