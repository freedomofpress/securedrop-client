import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import fs from "fs";
import os from "os";
import path from "path";
import {
  FetchStatus,
  type GetSourceWithItemsOptions,
  type ItemMetadata,
  type SourceWithItems,
} from "../../../types";
import { Datastore } from "../../../main/datastore";
import conversationSlice, {
  fetchConversation,
  fetchOlderConversationItems,
  clearError,
  clearConversation,
  updateItem,
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
      filename: null,
      decrypted_size: null,
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
      filename: null,
      decrypted_size: null,
      fetch_progress: 512,
      fetch_status: 3,
    },
  ],
  hasMoreHistoricalItems: true,
  paginationGeneration: 10,
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
      plaintext: null,
      filename: "document.pdf",
      decrypted_size: null,
      fetch_progress: 2048,
      fetch_status: 3,
    },
  ],
  hasMoreHistoricalItems: false,
  paginationGeneration: 10,
};

function deferred<T>() {
  let resolve!: (value: T) => void;
  let reject!: (reason: unknown) => void;
  const promise = new Promise<T>((resolvePromise, rejectPromise) => {
    resolve = resolvePromise;
    reject = rejectPromise;
  });
  return { promise, reject, resolve };
}

const idleTraversalState = {
  traversalEpoch: 0,
  traversalSourceUuid: null,
  activeConversationRequest: null,
  activeOlderRequest: null,
};

describe("conversationSlice", () => {
  let store: ReturnType<typeof configureStore>;
  const mockGetSourceWithItems = vi.fn();
  const mockAddPendingSourceConversationSeen = vi.fn();
  const mockFinalizePendingSourceConversationSeen = vi.fn();
  const mockGetConversationPaginationGeneration = vi.fn();
  const mockGetSources = vi.fn();

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
      addPendingSourceConversationSeen: mockAddPendingSourceConversationSeen,
      finalizePendingSourceConversationSeen:
        mockFinalizePendingSourceConversationSeen,
      getConversationPaginationGeneration:
        mockGetConversationPaginationGeneration,
      getSources: mockGetSources,
    };

    // Default mock implementations
    mockGetSourceWithItems.mockResolvedValue(mockSourceWithItems);
    mockAddPendingSourceConversationSeen.mockResolvedValue(null);
    mockFinalizePendingSourceConversationSeen.mockResolvedValue(false);
    mockGetConversationPaginationGeneration.mockReturnValue(10);
    mockGetSources.mockResolvedValue({});
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
        hasMoreHistoricalItems: false,
        olderItemsLoading: false,
        ...idleTraversalState,
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
        hasMoreHistoricalItems: false,
        olderItemsLoading: false,
        ...idleTraversalState,
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
        hasMoreHistoricalItems: false,
        olderItemsLoading: false,
        ...idleTraversalState,
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

      expect(mockGetSourceWithItems).toHaveBeenCalledWith("source-1", {
        limit: 100,
      });
      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
      expect(state.lastFetchTime).toBeGreaterThan(0);
      expect(mockAddPendingSourceConversationSeen).toHaveBeenCalledWith(
        "source-1",
        2,
        expect.stringContaining("source-1:1:"),
      );
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

    it("discards an older navigation response and its seen effects", async () => {
      const sourceARequest = deferred<SourceWithItems>();
      mockGetSourceWithItems
        .mockReturnValueOnce(sourceARequest.promise)
        .mockResolvedValueOnce(mockSourceWithItems2);
      mockAddPendingSourceConversationSeen.mockResolvedValue("created");

      const sourceADispatch = (store.dispatch as any)(
        fetchConversation("source-1"),
      );
      await (store.dispatch as any)(fetchConversation("source-2"));
      mockAddPendingSourceConversationSeen.mockClear();
      mockGetSources.mockClear();

      sourceARequest.resolve(mockSourceWithItems);
      await sourceADispatch;

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems2);
      expect(state.traversalSourceUuid).toBe("source-2");
      expect(mockAddPendingSourceConversationSeen).not.toHaveBeenCalled();
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("rolls back a seen write completed after navigation", async () => {
      const seenWrite = deferred<string | null>();
      mockGetSourceWithItems.mockImplementation((sourceUuid: string) =>
        Promise.resolve(
          sourceUuid === "source-1"
            ? mockSourceWithItems
            : mockSourceWithItems2,
        ),
      );
      mockAddPendingSourceConversationSeen.mockImplementation(
        (sourceUuid: string) =>
          sourceUuid === "source-1" ? seenWrite.promise : Promise.resolve(null),
      );

      const staleDispatch = (store.dispatch as any)(
        fetchConversation("source-1"),
      );
      await vi.waitFor(() => {
        expect(mockAddPendingSourceConversationSeen).toHaveBeenCalled();
      });
      await (store.dispatch as any)(fetchConversation("source-2"));
      mockGetSources.mockClear();

      seenWrite.resolve("stale-seen-id");
      await staleDispatch;

      const staleToken = mockAddPendingSourceConversationSeen.mock.calls[0][2];
      expect(mockFinalizePendingSourceConversationSeen).toHaveBeenCalledWith(
        "source-1",
        staleToken,
        false,
      );
      expect(mockGetSources).not.toHaveBeenCalled();
      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems2);
      expect(state.loading).toBe(false);
    });

    it("refreshes from a seen event adopted by the current request", async () => {
      const staleSeenWrite = deferred<string | null>();
      mockAddPendingSourceConversationSeen
        .mockReturnValueOnce(staleSeenWrite.promise)
        .mockResolvedValueOnce("adopted-seen-id");

      const staleDispatch = (store.dispatch as any)(
        fetchConversation("source-1"),
      );
      await vi.waitFor(() => {
        expect(mockAddPendingSourceConversationSeen).toHaveBeenCalledTimes(1);
      });
      const currentDispatch = (store.dispatch as any)(
        fetchConversation("source-1"),
      );
      await currentDispatch;

      expect(mockGetSources).toHaveBeenCalledTimes(1);
      const currentToken =
        mockAddPendingSourceConversationSeen.mock.calls[1][2];
      expect(mockFinalizePendingSourceConversationSeen).toHaveBeenCalledWith(
        "source-1",
        currentToken,
        true,
      );

      staleSeenWrite.resolve("stale-seen-id");
      await staleDispatch;

      const staleToken = mockAddPendingSourceConversationSeen.mock.calls[0][2];
      expect(mockFinalizePendingSourceConversationSeen).toHaveBeenCalledWith(
        "source-1",
        staleToken,
        false,
      );
      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.loading).toBe(false);
    });

    it("binds initial results to the captured epoch when request IDs repeat", async () => {
      const stalePage = deferred<SourceWithItems>();
      const currentPage = deferred<SourceWithItems>();
      mockGetSourceWithItems
        .mockReturnValueOnce(stalePage.promise)
        .mockReturnValueOnce(currentPage.promise);
      const originalRandom = Math.random;
      Math.random = () => 0;
      try {
        const staleDispatch = (store.dispatch as any)(
          fetchConversation("source-1"),
        );
        const currentDispatch = (store.dispatch as any)(
          fetchConversation("source-1"),
        );
        expect(staleDispatch.requestId).toBe(currentDispatch.requestId);

        stalePage.resolve({
          ...mockSourceWithItems,
          data: {
            ...mockSourceWithItems.data,
            journalist_designation: "stale",
          },
        });
        await staleDispatch;
        currentPage.resolve({
          ...mockSourceWithItems,
          data: {
            ...mockSourceWithItems.data,
            journalist_designation: "current",
          },
        });
        await currentDispatch;

        const state = (store.getState() as any).conversation;
        expect(state.conversation.data.journalist_designation).toBe("current");
        expect(state.activeConversationRequest).toBeNull();
        expect(state.loading).toBe(false);
        expect(state.traversalEpoch).toBe(2);
        expect(mockAddPendingSourceConversationSeen).toHaveBeenCalledTimes(1);
      } finally {
        Math.random = originalRandom;
      }
    });

    it("re-reads an initial page changed before renderer fulfillment", async () => {
      const staleRead = deferred<SourceWithItems>();
      const currentPage: SourceWithItems = {
        ...mockSourceWithItems,
        items: [mockSourceWithItems.items[1]],
        paginationGeneration: 11,
      };
      mockGetSourceWithItems
        .mockReturnValueOnce(staleRead.promise)
        .mockResolvedValueOnce(currentPage);
      mockGetConversationPaginationGeneration.mockReturnValue(11);

      const dispatch = (store.dispatch as any)(fetchConversation("source-1"));
      staleRead.resolve(mockSourceWithItems);
      await dispatch;

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(2);
      expect(mockAddPendingSourceConversationSeen).toHaveBeenCalledTimes(1);
      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(currentPage);
      expect(state.loading).toBe(false);
    });

    it("removes a real seen event written after navigation", async () => {
      const dbDir = fs.mkdtempSync(path.join(os.tmpdir(), "seen-race-"));
      const realDb = new Datastore(
        {} as never,
        {
          deleteItemFs: async () => undefined,
          deleteSourceFs: async () => undefined,
        } as never,
        dbDir,
      );
      const sourceA = "10000000-0000-4000-8000-000000000000";
      const sourceB = "20000000-0000-4000-8000-000000000000";
      const itemUuid = "30000000-0000-4000-8000-000000000001";
      realDb.updateSources({
        [sourceA]: { ...mockSourceWithItems.data, uuid: sourceA },
        [sourceB]: { ...mockSourceWithItems2.data, uuid: sourceB },
      });
      realDb.updateItems({
        [itemUuid]: {
          interaction_count: 1,
          is_read: false,
          kind: "message",
          seen_by: [],
          size: 1,
          source: sourceA,
          uuid: itemUuid,
        },
      });
      const seenStarted = deferred<void>();
      const releaseSeen = deferred<void>();
      let refreshes = 0;
      (window as any).electronAPI = {
        addPendingSourceConversationSeen: async (
          sourceUuid: string,
          upperBound: number,
          token: string,
        ) => {
          if (sourceUuid === sourceA) {
            seenStarted.resolve();
            await releaseSeen.promise;
          }
          return realDb.addPendingSourceConversationSeen(
            sourceUuid,
            upperBound,
            token,
          );
        },
        finalizePendingSourceConversationSeen: async (
          sourceUuid: string,
          token: string,
          keep: boolean,
        ) =>
          realDb.finalizePendingSourceConversationSeen(sourceUuid, token, keep),
        getConversationPaginationGeneration: () =>
          realDb.getConversationPaginationGeneration(),
        getSourceWithItems: async (
          sourceUuid: string,
          options?: GetSourceWithItemsOptions,
        ) => realDb.getSourceWithItems(sourceUuid, options),
        getSources: async () => {
          refreshes += 1;
          return {};
        },
      };

      try {
        const staleDispatch = (store.dispatch as any)(
          fetchConversation(sourceA),
        );
        await seenStarted.promise;
        await (store.dispatch as any)(fetchConversation(sourceB));
        releaseSeen.resolve();
        await staleDispatch;

        const seenForA = realDb
          .getPendingEvents()
          .filter(
            (event) =>
              event.type === "source_conversation_seen" &&
              "source_uuid" in event.target &&
              event.target.source_uuid === sourceA,
          );
        expect(seenForA).toHaveLength(0);
        expect(refreshes).toBe(0);
        expect((store.getState() as any).conversation.conversation.uuid).toBe(
          sourceB,
        );
      } finally {
        realDb.close();
      }
    });
  });

  describe("fetchOlderConversationItems async thunk", () => {
    const olderItem = {
      ...mockSourceWithItems.items[0],
      uuid: "item-0",
      data: {
        ...mockSourceWithItems.items[0].data,
        uuid: "item-0",
        interaction_count: 0,
      },
    };
    const olderPage: SourceWithItems = {
      ...mockSourceWithItems,
      items: [olderItem],
      hasMoreHistoricalItems: false,
      paginationGeneration: 10,
    };

    it("merges a successful page and updates hasMore", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      mockGetSourceWithItems.mockResolvedValue(olderPage);

      const action = await (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );

      expect(mockGetSourceWithItems).toHaveBeenCalledWith("source-1", {
        limit: 100,
        beforeInteractionCount: 1,
        beforeItemUuid: "item-1",
        paginationGeneration: 10,
      });
      expect(action.payload.request.sourceUuid).toBe("source-1");
      const state = (store.getState() as any).conversation;
      expect(state.conversation.items.map((item: any) => item.uuid)).toEqual([
        "item-0",
        "item-1",
        "item-2",
      ]);
      expect(state.hasMoreHistoricalItems).toBe(false);
      expect(state.conversation.hasMoreHistoricalItems).toBe(false);
      expect(state.olderItemsLoading).toBe(false);
      expect(mockAddPendingSourceConversationSeen).toHaveBeenCalledTimes(1);
    });

    it("discards a stale fulfillment after switching sources", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      mockAddPendingSourceConversationSeen.mockResolvedValue("created");
      const sourceARequest = deferred<SourceWithItems>();
      mockGetSourceWithItems
        .mockReturnValueOnce(sourceARequest.promise)
        .mockResolvedValueOnce(mockSourceWithItems2);

      const sourceADispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      await (store.dispatch as any)(fetchConversation("source-2"));
      mockAddPendingSourceConversationSeen.mockClear();
      mockGetSources.mockClear();
      sourceARequest.resolve(olderPage);
      await sourceADispatch;

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems2);
      expect(state.conversation.items.map((item: any) => item.uuid)).toEqual([
        "item-3",
      ]);
      expect(state.hasMoreHistoricalItems).toBe(false);
      expect(state.olderItemsLoading).toBe(false);
      expect(mockAddPendingSourceConversationSeen).not.toHaveBeenCalled();
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("discards an A to B to A page without clearing the new request", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      const staleRequest = deferred<SourceWithItems>();
      const currentRequest = deferred<SourceWithItems>();
      const currentSourceA = {
        ...mockSourceWithItems,
        paginationGeneration: 30,
      };
      const currentOlderPage = {
        ...olderPage,
        paginationGeneration: 30,
      };
      mockGetSourceWithItems
        .mockReturnValueOnce(staleRequest.promise)
        .mockResolvedValueOnce(mockSourceWithItems2)
        .mockResolvedValueOnce(currentSourceA)
        .mockReturnValueOnce(currentRequest.promise);

      const staleDispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      await (store.dispatch as any)(fetchConversation("source-2"));
      mockGetConversationPaginationGeneration.mockReturnValue(30);
      await (store.dispatch as any)(fetchConversation("source-1"));
      const currentDispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      mockAddPendingSourceConversationSeen.mockClear();
      mockGetSources.mockClear();

      staleRequest.resolve(olderPage);
      await staleDispatch;

      let state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(currentSourceA);
      expect(state.olderItemsLoading).toBe(true);
      expect(state.activeOlderRequest).not.toBeNull();
      expect(mockAddPendingSourceConversationSeen).not.toHaveBeenCalled();
      expect(mockGetSources).not.toHaveBeenCalled();

      currentRequest.resolve(currentOlderPage);
      await currentDispatch;
      state = (store.getState() as any).conversation;
      expect(state.conversation.items.map((item: any) => item.uuid)).toEqual([
        "item-0",
        "item-1",
        "item-2",
      ]);
      expect(state.conversation.paginationGeneration).toBe(30);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("preserves hasMore when the request is rejected", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockRejectedValue(new Error("IPC failed"));

      await (store.dispatch as any)(fetchOlderConversationItems("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.hasMoreHistoricalItems).toBe(true);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("discards a stale rejection after switching sources", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      const sourceARequest = deferred<SourceWithItems>();
      mockGetSourceWithItems
        .mockReturnValueOnce(sourceARequest.promise)
        .mockResolvedValueOnce(mockSourceWithItems2);

      const sourceADispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      await (store.dispatch as any)(fetchConversation("source-2"));
      sourceARequest.reject(new Error("source A failed"));
      await sourceADispatch;

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems2);
      expect(state.hasMoreHistoricalItems).toBe(false);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("invalidates an older request when the conversation is cleared", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      const request = deferred<SourceWithItems>();
      mockGetSourceWithItems.mockReturnValue(request.promise);

      const dispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      store.dispatch(clearConversation());
      request.resolve(olderPage);
      await dispatch;

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toBeNull();
      expect(state.olderItemsLoading).toBe(false);
      expect(state.activeOlderRequest).toBeNull();
      expect(state.traversalSourceUuid).toBeNull();
    });

    it("suppresses a duplicate dispatch while a page is pending", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      const request = deferred<SourceWithItems>();
      mockGetSourceWithItems.mockReturnValue(request.promise);

      const firstDispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      const duplicateAction = await (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);
      expect(duplicateAction.meta.condition).toBe(true);
      request.resolve(olderPage);
      await firstDispatch;
      const state = (store.getState() as any).conversation;
      expect(state.conversation.items.map((item: any) => item.uuid)).toEqual([
        "item-0",
        "item-1",
        "item-2",
      ]);
      expect(state.hasMoreHistoricalItems).toBe(false);
    });

    it("replaces the traversal when the datastore generation changes", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      const restartedPage: SourceWithItems = {
        ...mockSourceWithItems,
        items: [olderItem],
        hasMoreHistoricalItems: true,
        paginationGeneration: 11,
        paginationRestarted: true,
      };
      mockGetSourceWithItems.mockResolvedValue(restartedPage);
      mockGetConversationPaginationGeneration.mockReturnValue(11);

      await (store.dispatch as any)(fetchOlderConversationItems("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(restartedPage);
      expect(state.hasMoreHistoricalItems).toBe(true);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("re-reads a page changed after its database read", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      const staleRead = deferred<SourceWithItems>();
      const restartedPage: SourceWithItems = {
        ...mockSourceWithItems,
        items: [mockSourceWithItems.items[1]],
        hasMoreHistoricalItems: true,
        paginationGeneration: 11,
        paginationRestarted: true,
      };
      mockGetSourceWithItems
        .mockReturnValueOnce(staleRead.promise)
        .mockResolvedValueOnce(restartedPage);

      const dispatch = (store.dispatch as any)(
        fetchOlderConversationItems("source-1"),
      );
      mockGetConversationPaginationGeneration.mockReturnValue(11);
      staleRead.resolve(olderPage);
      await dispatch;

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(2);
      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(restartedPage);
      expect(state.hasMoreHistoricalItems).toBe(true);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("rejects a real SQLite page mutated after read", async () => {
      const dbDir = fs.mkdtempSync(path.join(os.tmpdir(), "pagination-race-"));
      const realDb = new Datastore(
        {} as never,
        {
          deleteItemFs: async () => undefined,
          deleteSourceFs: async () => undefined,
        } as never,
        dbDir,
      );
      const sourceUuid = "10000000-0000-4000-8000-000000000000";
      const itemUuid = (index: number) =>
        `30000000-0000-4000-8000-${index.toString().padStart(12, "0")}`;
      const items: Record<string, ItemMetadata> = {};
      for (let index = 1; index <= 151; index += 1) {
        const uuid = itemUuid(index);
        items[uuid] = {
          interaction_count: 100,
          is_read: false,
          kind: "message",
          seen_by: [],
          size: 1,
          source: sourceUuid,
          uuid,
        };
      }
      realDb.updateSources({
        [sourceUuid]: { ...mockSourceWithItems.data, uuid: sourceUuid },
      });
      realDb.updateItems(items);
      const held = deferred<SourceWithItems>();
      let holdOlderPage = false;
      let stalePage: SourceWithItems | undefined;
      (window as any).electronAPI = {
        addPendingSourceConversationSeen: async () => null,
        finalizePendingSourceConversationSeen: async () => false,
        getConversationPaginationGeneration: () =>
          realDb.getConversationPaginationGeneration(),
        getSourceWithItems: async (
          requestedSourceUuid: string,
          options?: GetSourceWithItemsOptions,
        ) => {
          const page = realDb.getSourceWithItems(requestedSourceUuid, options);
          if (holdOlderPage && options?.beforeItemUuid !== undefined) {
            holdOlderPage = false;
            stalePage = page;
            return held.promise;
          }
          return page;
        },
        getSources: async () => ({}),
      };

      try {
        await (store.dispatch as any)(fetchConversation(sourceUuid));
        holdOlderPage = true;
        const olderDispatch = (store.dispatch as any)(
          fetchOlderConversationItems(sourceUuid),
        );
        expect(stalePage?.items).toHaveLength(51);
        const deletedUuid = stalePage!.items[0].uuid;
        realDb.updateItems({ [deletedUuid]: null });
        const currentGeneration = realDb.getConversationPaginationGeneration();

        held.resolve(stalePage!);
        await olderDispatch;

        const state = (store.getState() as any).conversation;
        expect(state.conversation.paginationGeneration).toBe(currentGeneration);
        expect(
          state.conversation.items.some(
            (item: { uuid: string }) => item.uuid === deletedUuid,
          ),
        ).toBe(false);
        expect(state.conversation.items).toHaveLength(100);
        expect(state.hasMoreHistoricalItems).toBe(true);
      } finally {
        realDb.close();
      }
    });

    it("converges after repeated generation changes become quiescent", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockClear();
      const restartAt11: SourceWithItems = {
        ...olderPage,
        paginationGeneration: 11,
        paginationRestarted: true,
      };
      const restartAt12: SourceWithItems = {
        ...olderPage,
        paginationGeneration: 12,
        paginationRestarted: true,
      };
      mockGetSourceWithItems
        .mockResolvedValueOnce(olderPage)
        .mockResolvedValueOnce(restartAt11)
        .mockResolvedValueOnce(restartAt12);
      mockGetConversationPaginationGeneration
        .mockReturnValueOnce(11)
        .mockReturnValueOnce(12)
        .mockReturnValue(12);

      await (store.dispatch as any)(fetchOlderConversationItems("source-1"));

      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(3);
      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(restartAt12);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("discards a non-restart page from a different generation", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockResolvedValue({
        ...olderPage,
        paginationGeneration: 11,
      });
      mockGetConversationPaginationGeneration.mockReturnValue(11);

      await (store.dispatch as any)(fetchOlderConversationItems("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.hasMoreHistoricalItems).toBe(true);
      expect(state.olderItemsLoading).toBe(false);
    });

    it("discards a page whose returned source differs from the request", async () => {
      await (store.dispatch as any)(fetchConversation("source-1"));
      mockGetSourceWithItems.mockResolvedValue({
        ...olderPage,
        uuid: "source-2",
      });

      await (store.dispatch as any)(fetchOlderConversationItems("source-1"));

      const state = (store.getState() as any).conversation;
      expect(state.conversation).toEqual(mockSourceWithItems);
      expect(state.hasMoreHistoricalItems).toBe(true);
      expect(state.olderItemsLoading).toBe(false);
    });
  });

  describe("selectors", () => {
    const mockSessionState = {
      status: SessionStatus.Unauth,
      authData: undefined,
    };

    const mockState = {
      session: mockSessionState,
      drafts: {
        drafts: {},
      },
      sources: {
        sources: {},
        activeSourceUuid: null,
        loading: false,
        error: null,
        conversationIndicators: {},
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
        hasMoreHistoricalItems: false,
        olderItemsLoading: false,
        ...idleTraversalState,
      },
      sync: {
        error: null,
        lastSyncStarted: null,
        lastSyncFinished: null,
        status: null,
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

  describe("updateItem reducer — worker updates", () => {
    const fileItem = {
      uuid: "file-1",
      data: {
        kind: "file" as const,
        uuid: "file-1",
        source: "source-1",
        size: 1024,
        is_read: false,
        seen_by: [],
        interaction_count: 1,
      },
      plaintext: null,
      filename: null,
      decrypted_size: null,
      fetch_progress: 0,
      fetch_status: FetchStatus.DownloadInProgress,
    };

    const sourceWithFile: SourceWithItems = {
      ...mockSourceWithItems,
      items: [fileItem],
    };

    const stateWithFile: ConversationState = {
      conversation: sourceWithFile,
      loading: false,
      error: null,
      lastFetchTime: null,
      hasMoreHistoricalItems: false,
      olderItemsLoading: false,
      ...idleTraversalState,
    };

    it("does not resurrect a Cancelled item", () => {
      const canceledState: ConversationState = {
        ...stateWithFile,
        conversation: {
          ...sourceWithFile,
          items: [{ ...fileItem, fetch_status: FetchStatus.Cancelled }],
        },
      };
      const staleUpdate = {
        ...fileItem,
        fetch_status: FetchStatus.DownloadInProgress,
      };
      const newState = conversationSlice(
        canceledState,
        updateItem(staleUpdate),
      );
      expect(newState.conversation?.items[0].fetch_status).toBe(
        FetchStatus.Cancelled,
      );
    });

    it("applies legitimate terminal transitions from the worker", () => {
      const inProgressState: ConversationState = {
        ...stateWithFile,
        conversation: {
          ...sourceWithFile,
          items: [
            { ...fileItem, fetch_status: FetchStatus.DownloadInProgress },
          ],
        },
      };
      // Worker marks download as terminally failed
      const failedUpdate = {
        ...fileItem,
        fetch_status: FetchStatus.FailedTerminal,
      };
      const newState = conversationSlice(
        inProgressState,
        updateItem(failedUpdate),
      );
      expect(newState.conversation?.items[0].fetch_status).toBe(
        FetchStatus.FailedTerminal,
      );
    });

    it("applies Complete status update from the worker", () => {
      const inProgressState: ConversationState = {
        ...stateWithFile,
        conversation: {
          ...sourceWithFile,
          items: [
            { ...fileItem, fetch_status: FetchStatus.DecryptionInProgress },
          ],
        },
      };
      const completedUpdate = {
        ...fileItem,
        fetch_status: FetchStatus.Complete,
      };
      const newState = conversationSlice(
        inProgressState,
        updateItem(completedUpdate),
      );
      expect(newState.conversation?.items[0].fetch_status).toBe(
        FetchStatus.Complete,
      );
    });
  });
});
