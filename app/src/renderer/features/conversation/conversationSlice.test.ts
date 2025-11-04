/* eslint-disable @typescript-eslint/no-explicit-any */
import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import type { SourceWithItems } from "../../../types";
import conversationSlice, {
  fetchConversation,
  clearError,
  clearConversation,
  selectConversation,
  selectConversationLoading,
  type ConversationState,
} from "./conversationSlice";
import { SessionStatus } from "../session/sessionSlice";

// Mock conversation data
const mockSourceWithItems: SourceWithItems = {
  uuid: "source-1",
  data: {
    fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    journalist_designation: "alice wonderland",
    last_updated: "2024-01-15T10:30:00Z",
    public_key:
      "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
    uuid: "source-1",
  },
  items: [
    {
      uuid: "item-1",
      data: {
        kind: "message",
        uuid: "item-1",
        source: "source-1",
        size: 1024,
        is_read: false,
        seen_by: [],
        interaction_count: 1,
      },
      plaintext: "Hello from Alice!",
      fetch_progress: 1024,
      fetch_status: 3,
    },
    {
      uuid: "item-2",
      data: {
        kind: "reply",
        uuid: "item-2",
        source: "source-1",
        size: 512,
        journalist_uuid: "journalist-1",
        is_deleted_by_source: false,
        seen_by: ["journalist-1"],
        interaction_count: 2,
      },
      plaintext: "Hi Alice, thanks for reaching out.",
      fetch_progress: 512,
      fetch_status: 3,
    },
  ],
};

const mockSourceWithItems2: SourceWithItems = {
  uuid: "source-2",
  data: {
    fingerprint: "EFGH5678IJKL9012MNOP3456QRST7890ABCD1234",
    is_starred: true,
    is_seen: true,
    has_attachment: true,
    journalist_designation: "bob builder",
    last_updated: "2024-01-16T15:45:00Z",
    public_key:
      "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
    uuid: "source-2",
  },
  items: [
    {
      uuid: "item-3",
      data: {
        kind: "file",
        uuid: "item-3",
        source: "source-2",
        size: 2048,
        is_read: true,
        seen_by: ["journalist-1"],
        interaction_count: 1,
      },
      filename: "document.pdf",
      fetch_progress: 2048,
      fetch_status: 3,
    },
  ],
};

describe("conversationSlice", () => {
  let store: ReturnType<typeof configureStore>;
  const mockGetSourceWithItems = vi.fn();
  const mockAddPendingItemsSeenBatch = vi.fn();

  beforeEach(() => {
    // Create a test store with conversations slice
    store = configureStore({
      reducer: {
        conversation: conversationSlice,
      },
    });

    // Reset mocks
    vi.clearAllMocks();

    // Mock electronAPI
    (window as any).electronAPI = {
      getSourceWithItems: mockGetSourceWithItems,
      addPendingItemsSeenBatch: mockAddPendingItemsSeenBatch,
    };

    // Default mock implementations
    mockGetSourceWithItems.mockResolvedValue(mockSourceWithItems);
    mockAddPendingItemsSeenBatch.mockResolvedValue([]);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("initial state", () => {
    it("has correct initial state", () => {
      const state = (store.getState() as any).conversation;
      expect(state).toEqual({
        conversation: null,
        loading: false,
        error: null,
        lastFetchTime: null,
      });
    });
  });

  describe("clearError action", () => {
    it("clears the error state", () => {
      // First, set an error state
      const initialState: ConversationState = {
        conversation: null,
        loading: false,
        error: "Some error message",
        lastFetchTime: null,
      };

      const action = clearError();
      const newState = conversationSlice(initialState, action);

      expect(newState.error).toBeNull();
      expect(newState.conversation).toBeNull();
      expect(newState.loading).toBe(false);
      expect(newState.lastFetchTime).toBeNull();
    });
  });

  describe("clearConversation action", () => {
    it("clears the current conversation", () => {
      const initialState: ConversationState = {
        conversation: mockSourceWithItems,
        loading: false,
        error: null,
        lastFetchTime: 123456789,
      };

      const action = clearConversation();
      const newState = conversationSlice(initialState, action);

      expect(newState.conversation).toBeNull();
      expect(newState.lastFetchTime).toBeNull();
    });
  });

  describe("fetchConversation async thunk", () => {
    it("handles successful fetch", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));

      expect(mockGetSourceWithItems).toHaveBeenCalledWith("source-1");
      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
      expect(state.lastFetchTime).toBeGreaterThan(0);
    });

    it("handles fetch error", async () => {
      const errorMessage = "Failed to fetch conversation";
      mockGetSourceWithItems.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(fetchConversation("source-1"));

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toBeNull();
      expect(state.loading).toBe(false);
      expect(state.error).toBe(errorMessage);
    });

    it("sets loading state during fetch", async () => {
      // Create a promise that we can control
      let resolveGetSourceWithItems!: (value: SourceWithItems) => void;
      const getSourceWithItemsPromise = new Promise<SourceWithItems>(
        (resolve) => {
          resolveGetSourceWithItems = resolve;
        },
      );
      mockGetSourceWithItems.mockReturnValue(getSourceWithItemsPromise);

      const action = fetchConversation("source-1");
      const dispatchPromise = (store.dispatch as any)(action);

      // Check loading state is true while pending
      expect((store.getState() as any).conversation.loading).toBe(true);
      expect((store.getState() as any).conversation.error).toBeNull();

      // Resolve the promise
      resolveGetSourceWithItems!(mockSourceWithItems);
      await dispatchPromise;

      // Check loading state is false after completion
      expect((store.getState() as any).conversation.loading).toBe(false);
    });
  });

  describe("selectors", () => {
    const mockSessionState = {
      status: SessionStatus.Unauth,
      authData: undefined,
    };

    const mockState = {
      session: mockSessionState,
      sources: {
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: null,
      },
      journalists: {
        journalists: [],
        loading: false,
        error: null,
      },
      conversation: {
        conversation: mockSourceWithItems,
        loading: false,
        error: "Test error",
        lastFetchTime: 123456789,
      },
      sync: {
        loading: false,
        error: null,
        lastFetchTime: null,
      },
    };

    it("selectConversation returns conversation for matching UUID", () => {
      expect(selectConversation(mockState, "source-1")).toEqual(
        mockSourceWithItems,
      );
      expect(selectConversation(mockState, "source-2")).toBeNull();
      expect(selectConversation(mockState, "nonexistent")).toBeNull();
    });

    it("selectConversationLoading returns loading state", () => {
      expect(selectConversationLoading(mockState)).toBe(false);
    });
  });

  describe("error handling edge cases", () => {
    it("handles undefined error message", async () => {
      const errorWithoutMessage = new Error();
      errorWithoutMessage.message = "";
      mockGetSourceWithItems.mockRejectedValue(errorWithoutMessage);

      await (store.dispatch as any)(fetchConversation("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.error).toBe("Failed to fetch conversation");
    });

    it("handles non-Error rejection", async () => {
      mockGetSourceWithItems.mockRejectedValue("String error");

      await (store.dispatch as any)(fetchConversation("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.error).toBe("String error");
    });
  });

  describe("state transitions", () => {
    it("clears previous error when new fetch starts", async () => {
      // First, create an error state
      mockGetSourceWithItems.mockRejectedValue(new Error("First error"));
      await (store.dispatch as any)(fetchConversation("source-1"));
      expect((store.getState() as any).conversation.error).toBe("First error");

      // Then make a successful call
      mockGetSourceWithItems.mockResolvedValue(mockSourceWithItems);
      await (store.dispatch as any)(fetchConversation("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.error).toBeNull();
      expect(state.conversation).toEqual(mockSourceWithItems);
    });

    it("updates lastFetchTime on successful operations", async () => {
      const beforeTime = Date.now();

      await (store.dispatch as any)(fetchConversation("source-1"));

      const afterTime = Date.now();
      const state = (store.getState() as any).conversation;

      expect(state.lastFetchTime).toBeGreaterThanOrEqual(beforeTime);
      expect(state.lastFetchTime).toBeLessThanOrEqual(afterTime);
    });

    it("does not update lastFetchTime on failed operations", async () => {
      mockGetSourceWithItems.mockRejectedValue(new Error("Failed"));

      await (store.dispatch as any)(fetchConversation("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.lastFetchTime).toBeNull();
    });
  });

  describe("concurrent operations", () => {
    it("handles multiple fetchConversation calls correctly", async () => {
      mockGetSourceWithItems
        .mockResolvedValueOnce(mockSourceWithItems)
        .mockResolvedValueOnce(mockSourceWithItems2);

      // First call
      await (store.dispatch as any)(fetchConversation("source-1"));
      // Second call overwrites the first
      await (store.dispatch as any)(fetchConversation("source-2"));

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(2);

      const state = (store.getState() as any).conversation;
      // Only the last conversation should be stored
      expect(state.conversation).toEqual(mockSourceWithItems2);
      expect(state.loading).toBe(false);
    });
  });
});
