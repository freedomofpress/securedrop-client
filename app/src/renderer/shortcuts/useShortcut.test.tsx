import { describe, it, expect, vi } from "vitest";
import { fireEvent, renderHook } from "@testing-library/react";
import { useShortcut } from "./useShortcut";

describe("useShortcut", () => {
  it("fires callback when registered key combination is pressed", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback));

    fireEvent.keyDown(document, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(callback).toHaveBeenCalledTimes(1);
  });

  it("does not fire callback for unrelated keys", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback));

    fireEvent.keyDown(document, { key: "a", code: "KeyA", ctrlKey: true });

    expect(callback).not.toHaveBeenCalled();
  });

  it("merges extraOptions with registry options", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback, { enabled: false }));

    fireEvent.keyDown(document, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(callback).not.toHaveBeenCalled();
  });

  it("blocks shortcuts when a text input is focused", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback));

    const input = document.createElement("input");
    input.type = "text";
    document.body.appendChild(input);
    input.focus();

    fireEvent.keyDown(input, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(callback).not.toHaveBeenCalled();
    document.body.removeChild(input);
  });

  it("blocks shortcuts when a textarea is focused", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback));

    const textarea = document.createElement("textarea");
    document.body.appendChild(textarea);
    textarea.focus();

    fireEvent.keyDown(textarea, { key: "q", code: "KeyQ", ctrlKey: true });

    expect(callback).not.toHaveBeenCalled();
    document.body.removeChild(textarea);
  });

  it("allows shortcuts on non-text inputs (checkbox, radio, button)", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("quit", callback));

    for (const type of ["checkbox", "radio", "button"]) {
      callback.mockClear();
      const input = document.createElement("input");
      input.type = type;
      document.body.appendChild(input);
      input.focus();

      fireEvent.keyDown(input, { key: "q", code: "KeyQ", ctrlKey: true });

      expect(callback).toHaveBeenCalledTimes(1);
      document.body.removeChild(input);
    }
  });

  it("allows shortcuts on elements with enableOnFormTags override", () => {
    const callback = vi.fn();
    // sendReply has enableOnFormTags: ["TEXTAREA"]
    renderHook(() => useShortcut("sendReply", callback));

    const textarea = document.createElement("textarea");
    document.body.appendChild(textarea);
    textarea.focus();

    fireEvent.keyDown(textarea, {
      key: "Enter",
      code: "Enter",
      ctrlKey: true,
    });

    expect(callback).toHaveBeenCalledTimes(1);
    document.body.removeChild(textarea);
  });

  it("still blocks textarea for shortcuts without enableOnFormTags override", () => {
    const callback = vi.fn();
    renderHook(() => useShortcut("downloadAll", callback));

    const textarea = document.createElement("textarea");
    document.body.appendChild(textarea);
    textarea.focus();

    fireEvent.keyDown(textarea, { key: "d", code: "KeyD", ctrlKey: true });

    expect(callback).not.toHaveBeenCalled();
    document.body.removeChild(textarea);
  });
});
