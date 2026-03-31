import { describe, it, expect, vi } from "vitest";
import { fireEvent, renderHook } from "@testing-library/react";
import { useMainContentShortcuts } from "./useMainContentShortcuts";

describe("useMainContentShortcuts", () => {
  const createHandlers = (enabled: boolean) => ({
    onDeleteSource: vi.fn(),
    onSendReply: vi.fn(),
    onDownloadAll: vi.fn(),
    enabled,
  });

  it("fires onDeleteSource on Ctrl+Delete when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useMainContentShortcuts(handlers));

    fireEvent.keyDown(document, {
      key: "Delete",
      code: "Delete",
      ctrlKey: true,
    });

    expect(handlers.onDeleteSource).toHaveBeenCalledTimes(1);
  });

  it("fires onSendReply on Ctrl+Enter when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useMainContentShortcuts(handlers));

    fireEvent.keyDown(document, {
      key: "Enter",
      code: "Enter",
      ctrlKey: true,
    });

    expect(handlers.onSendReply).toHaveBeenCalledTimes(1);
  });

  it("fires onDownloadAll on Ctrl+D when enabled", () => {
    const handlers = createHandlers(true);
    renderHook(() => useMainContentShortcuts(handlers));

    fireEvent.keyDown(document, { key: "d", code: "KeyD", ctrlKey: true });

    expect(handlers.onDownloadAll).toHaveBeenCalledTimes(1);
  });

  it("does NOT fire any handler when disabled", () => {
    const handlers = createHandlers(false);
    renderHook(() => useMainContentShortcuts(handlers));

    fireEvent.keyDown(document, {
      key: "Delete",
      code: "Delete",
      ctrlKey: true,
    });
    fireEvent.keyDown(document, {
      key: "Enter",
      code: "Enter",
      ctrlKey: true,
    });
    fireEvent.keyDown(document, { key: "d", code: "KeyD", ctrlKey: true });

    expect(handlers.onDeleteSource).not.toHaveBeenCalled();
    expect(handlers.onSendReply).not.toHaveBeenCalled();
    expect(handlers.onDownloadAll).not.toHaveBeenCalled();
  });

  it("respects enabled toggle via rerender", () => {
    const handlers = createHandlers(false);
    const { rerender } = renderHook((props) => useMainContentShortcuts(props), {
      initialProps: handlers,
    });

    fireEvent.keyDown(document, { key: "d", code: "KeyD", ctrlKey: true });
    expect(handlers.onDownloadAll).not.toHaveBeenCalled();

    // Enable
    rerender({ ...handlers, enabled: true });

    fireEvent.keyDown(document, { key: "d", code: "KeyD", ctrlKey: true });
    expect(handlers.onDownloadAll).toHaveBeenCalledTimes(1);
  });
});
