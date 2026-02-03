import { describe, it, expect } from "vitest";
import draftsReducer, { setDraft, clearDraft } from "./draftsSlice";
import type { DraftsState } from "./draftsSlice";
import { setUnauth } from "../session/sessionSlice";
import { fetchSources } from "../sources/sourcesSlice";
import type { Source } from "../../../types";

describe("draftsSlice", () => {
  const emptyState: DraftsState = { drafts: {} };

  it("should have empty initial state", () => {
    const result = draftsReducer(undefined, { type: "unknown" });
    expect(result).toEqual(emptyState);
  });

  describe("setDraft", () => {
    it("should set source draft", () => {
      const result = draftsReducer(
        emptyState,
        setDraft({ sourceUuid: "source-1", content: "hello" }),
      );
      expect(result.drafts["source-1"]).toBe("hello");
    });

    it("should update existing draft", () => {
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

    it("should delete key on empty content", () => {
      const state: DraftsState = { drafts: { "source-1": "hello" } };
      const result = draftsReducer(
        state,
        setDraft({ sourceUuid: "source-1", content: "" }),
      );
      expect(result.drafts).not.toHaveProperty("source-1");
    });
  });

  describe("clearDraft", () => {
    it("should remove draft for a source", () => {
      const state: DraftsState = { drafts: { "source-1": "hello" } };
      const result = draftsReducer(state, clearDraft("source-1"));
      expect(result.drafts).not.toHaveProperty("source-1");
    });

    it("should no-op for non-existent source", () => {
      const result = draftsReducer(emptyState, clearDraft("source-1"));
      expect(result).toEqual(emptyState);
    });
  });

  describe("clearDrafts", () => {
    it("should clear all drafts on setUnauth", () => {
      const state: DraftsState = {
        drafts: { "source-1": "draft one", "source-2": "draft two" },
      };
      const result = draftsReducer(state, setUnauth(undefined));
      expect(result.drafts).toEqual({});
    });

    it("should clear drafts for deleted sources", () => {
      const state: DraftsState = {
        drafts: {
          "source-1": "keep this",
          "source-2": "delete this",
          "source-3": "delete this too",
        },
      };
      const sources: Source[] = [
        {
          uuid: "source-1",
          data: {
            uuid: "source-1",
            journalist_designation: "test",
            is_starred: false,
            is_seen: false,
            has_attachment: false,
            last_updated: "2025-01-01",
            public_key: "key",
            fingerprint: "fp",
          },
          isRead: false,
          hasAttachment: false,
          messagePreview: null,
        },
      ];
      const result = draftsReducer(state, fetchSources.fulfilled(sources, ""));
      expect(result.drafts).toEqual({ "source-1": "keep this" });
    });

    it("should keep all drafts when no sources are deleted", () => {
      const state: DraftsState = {
        drafts: { "source-1": "one", "source-2": "two" },
      };
      const sources: Source[] = [
        {
          uuid: "source-1",
          data: {
            uuid: "source-1",
            journalist_designation: "test1",
            is_starred: false,
            is_seen: false,
            has_attachment: false,
            last_updated: "2025-01-01",
            public_key: "key",
            fingerprint: "fp",
          },
          isRead: false,
          hasAttachment: false,
          messagePreview: null,
        },
        {
          uuid: "source-2",
          data: {
            uuid: "source-2",
            journalist_designation: "test2",
            is_starred: false,
            is_seen: false,
            has_attachment: false,
            last_updated: "2025-01-01",
            public_key: "key",
            fingerprint: "fp",
          },
          isRead: false,
          hasAttachment: false,
          messagePreview: null,
        },
      ];
      const result = draftsReducer(state, fetchSources.fulfilled(sources, ""));
      expect(result.drafts).toEqual({ "source-1": "one", "source-2": "two" });
    });
  });
});
