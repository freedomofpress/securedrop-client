import { describe, it, expect, beforeEach, vi } from "vitest";
import draftsReducer, { setDraft, clearDraft } from "./draftsSlice";
import type { DraftsState } from "./draftsSlice";

describe("draftsSlice", () => {
  const emptyState: DraftsState = { drafts: {} };

  it("should have empty initial state when localStorage is empty", () => {
    const result = draftsReducer(undefined, { type: "unknown" });
    expect(result).toEqual(emptyState);
  });

  describe("setDraft", () => {
    it("set source draft", () => {
      const result = draftsReducer(
        emptyState,
        setDraft({ sourceUuid: "source-1", content: "hello" }),
      );
      expect(result.drafts["source-1"]).toBe("hello");
    });

    it("update existing draft", () => {
      const state: DraftsState = {
        drafts: { "source-1": "one", "source-2": "two" },
      };
      const result = draftsReducer(
        state,
        setDraft({ sourceUuid: "source-1", content: "updated" }),
      );
      expect(result.drafts["source-1"]).toBe("updated");
      expect(result.drafts["source-2"]).toBe("two");
    });

    it("delete key on empty content", () => {
      const state: DraftsState = { drafts: { "source-1": "hello" } };
      const result = draftsReducer(
        state,
        setDraft({ sourceUuid: "source-1", content: "" }),
      );
      expect(result.drafts).not.toHaveProperty("source-1");
    });
  });

  describe("clearDraft", () => {
    it("remove draft for a source", () => {
      const state: DraftsState = { drafts: { "source-1": "hello" } };
      const result = draftsReducer(state, clearDraft("source-1"));
      expect(result.drafts).not.toHaveProperty("source-1");
    });

    it("no-op for non-existent source", () => {
      const result = draftsReducer(emptyState, clearDraft("source-1"));
      expect(result).toEqual(emptyState);
    });
  });
});

describe("draftsSlice load from localStorage", () => {
  beforeEach(() => {
    vi.resetModules();
  });

  it("should load from localStorage on import", async () => {
    const data = { "source-1": "saved draft" };
    vi.spyOn(Storage.prototype, "getItem").mockReturnValue(
      JSON.stringify(data),
    );

    const { default: reducer } = await import("./draftsSlice");
    const state = reducer(undefined, { type: "unknown" });
    expect(state.drafts).toEqual(data);

    vi.restoreAllMocks();
  });

  it("should default to empty object on invalid JSON", async () => {
    vi.spyOn(Storage.prototype, "getItem").mockReturnValue("not-json");

    const { default: reducer } = await import("./draftsSlice");
    const state = reducer(undefined, { type: "unknown" });
    expect(state.drafts).toEqual({});

    vi.restoreAllMocks();
  });
});
