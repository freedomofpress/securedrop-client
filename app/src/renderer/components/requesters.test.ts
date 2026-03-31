import { describe, it, expect, vi, beforeEach } from "vitest";
import { requestQuit, setQuitHandler } from "./quitRequester";
import { requestHelp, setHelpHandler } from "./helpRequester";

describe("quitRequester", () => {
  beforeEach(() => {
    setQuitHandler(null);
  });

  it("calls the registered handler when requestQuit is called", () => {
    const handler = vi.fn();
    setQuitHandler(handler);

    requestQuit();

    expect(handler).toHaveBeenCalledTimes(1);
  });

  it("does not throw when no handler is registered", () => {
    expect(() => requestQuit()).not.toThrow();
  });

  it("clears handler when set to null", () => {
    const handler = vi.fn();
    setQuitHandler(handler);
    setQuitHandler(null);

    requestQuit();

    expect(handler).not.toHaveBeenCalled();
  });
});

describe("helpRequester", () => {
  beforeEach(() => {
    setHelpHandler(null);
  });

  it("calls the registered handler when requestHelp is called", () => {
    const handler = vi.fn();
    setHelpHandler(handler);

    requestHelp();

    expect(handler).toHaveBeenCalledTimes(1);
  });

  it("does not throw when no handler is registered", () => {
    expect(() => requestHelp()).not.toThrow();
  });

  it("clears handler when set to null", () => {
    const handler = vi.fn();
    setHelpHandler(handler);
    setHelpHandler(null);

    requestHelp();

    expect(handler).not.toHaveBeenCalled();
  });
});
