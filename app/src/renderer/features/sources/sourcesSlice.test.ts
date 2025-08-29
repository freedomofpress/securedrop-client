/* eslint-disable @typescript-eslint/no-explicit-any */
import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import type { Source as SourceType } from "../../../types";
import sourcesSlice, {
  fetchSources,
  syncSources,
  clearError,
  setActiveSource,
  clearActiveSource,
  selectSources,
  selectActiveSourceUuid,
  selectSourcesLoading,
  type SourcesState,
} from "./sourcesSlice";
import sessionSlice, {
  SessionStatus,
  type SessionState,
} from "../session/sessionSlice";
import conversationSlice from "../conversation/conversationSlice";

// Mock data matching the structure from test-component-setup.tsx
const mockSources: SourceType[] = [
  {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      journalist_designation: "multiplicative conditionality",
      last_updated: "2024-01-15T10:30:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-1",
    },
    isRead: false,
    hasAttachment: false,
    showMessagePreview: false,
    messagePreview: "",
  },
  {
    uuid: "source-2",
    data: {
      fingerprint: "1234ABCD5678EFGH9012IJKL3456MNOP7890QRST",
      is_starred: true,
      journalist_designation: "piezoelectric crockery",
      last_updated: "2024-01-14T15:45:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-2",
    },
    isRead: true,
    hasAttachment: true,
    showMessagePreview: true,
    messagePreview: "Hello from source 2",
  },
];

describe("sourcesSlice", () => {
  let store: ReturnType<typeof configureStore>;
  const mockGetSources = vi.fn();
  const mockSyncMetadata = vi.fn();

  beforeEach(() => {
    // Create a test store with sources, session, and conversations slices for proper typing
    store = configureStore({
      reducer: {
        sources: sourcesSlice,
        session: sessionSlice,
        conversation: conversationSlice,
      },
    });

    // Reset mocks
    vi.clearAllMocks();

    // Mock electronAPI
    (window as any).electronAPI = {
      getSources: mockGetSources,
      syncMetadata: mockSyncMetadata,
      getSourceWithItems: vi.fn().mockResolvedValue({
        uuid: "source-1",
        data: mockSources[0].data,
        items: [],
      }),
    };

    // Default mock implementations
    mockGetSources.mockResolvedValue(mockSources);
    mockSyncMetadata.mockResolvedValue(undefined);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("initial state", () => {
    it("has correct initial state", () => {
      const state = (store.getState() as any).sources;
      expect(state).toEqual({
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: null,
        lastSyncTime: null,
      });
    });
  });

  describe("clearError action", () => {
    it("clears the error state", () => {
      // First, set an error state
      const initialState: SourcesState = {
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: "Some error message",
        lastSyncTime: null,
      };

      const action = clearError();
      const newState = sourcesSlice(initialState, action);

      expect(newState.error).toBeNull();
      expect(newState.sources).toEqual([]);
      expect(newState.activeSourceUuid).toBeNull();
      expect(newState.loading).toBe(false);
      expect(newState.lastSyncTime).toBeNull();
    });
  });

  describe("setActiveSource action", () => {
    it("sets the active source UUID", () => {
      const initialState: SourcesState = {
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: null,
        lastSyncTime: null,
      };

      const action = setActiveSource("source-1");
      const newState = sourcesSlice(initialState, action);

      expect(newState.activeSourceUuid).toBe("source-1");
    });
  });

  describe("clearActiveSource action", () => {
    it("clears the active source UUID", () => {
      const initialState: SourcesState = {
        sources: [],
        activeSourceUuid: "source-1",
        loading: false,
        error: null,
        lastSyncTime: null,
      };

      const action = clearActiveSource();
      const newState = sourcesSlice(initialState, action);

      expect(newState.activeSourceUuid).toBeNull();
    });
  });

  describe("fetchSources async thunk", () => {
    it("handles successful fetch", async () => {
      await (store.dispatch as any)(fetchSources());

      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
      expect(state.lastSyncTime).toBeGreaterThan(0);
    });

    it("handles fetch error", async () => {
      const errorMessage = "Failed to fetch sources";
      mockGetSources.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(fetchSources());

      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);
      expect(state.error).toBe(errorMessage);
      expect(state.lastSyncTime).toBeNull();
    });

    it("sets loading state during fetch", async () => {
      // Create a promise that we can control
      let resolveGetSources!: (value: SourceType[]) => void;
      const getSourcesPromise = new Promise<SourceType[]>((resolve) => {
        resolveGetSources = resolve;
      });
      mockGetSources.mockReturnValue(getSourcesPromise);

      const action = fetchSources();
      const dispatchPromise = (store.dispatch as any)(action);

      // Check loading state is true while pending
      expect((store.getState() as any).sources.loading).toBe(true);
      expect((store.getState() as any).sources.error).toBeNull();

      // Resolve the promise
      resolveGetSources!(mockSources);
      await dispatchPromise;

      // Check loading state is false after completion
      expect((store.getState() as any).sources.loading).toBe(false);
    });
  });

  describe("syncSources async thunk", () => {
    it("handles successful sync with auth token", async () => {
      const authToken = "test-auth-token";
      const action = syncSources(authToken);
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledWith({ authToken });
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
      expect(state.lastSyncTime).toBeGreaterThan(0);
    });

    it("handles sync failure without auth token", async () => {
      const errorMessage = "Authentication required";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(syncSources(undefined));

      expect(mockSyncMetadata).toHaveBeenCalledWith({ authToken: undefined });
      expect(mockGetSources).not.toHaveBeenCalled();

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);
      expect(state.error).toBe(errorMessage);
    });

    it("handles sync metadata error", async () => {
      const errorMessage = "Failed to sync metadata";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      const action = syncSources("test-token");
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);
      expect(state.error).toBe(errorMessage);
    });

    it("handles getSources error after successful sync", async () => {
      const errorMessage = "Failed to get sources";
      mockGetSources.mockRejectedValue(new Error(errorMessage));

      const action = syncSources("test-token");
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);
      expect(state.error).toBe(errorMessage);
    });

    it("sets loading state during sync", async () => {
      // Create promises that we can control
      let resolveSyncMetadata!: () => void;
      let resolveGetSources!: (value: SourceType[]) => void;

      const syncMetadataPromise = new Promise<void>((resolve) => {
        resolveSyncMetadata = resolve;
      });
      const getSourcesPromise = new Promise<SourceType[]>((resolve) => {
        resolveGetSources = resolve;
      });

      mockSyncMetadata.mockReturnValue(syncMetadataPromise);
      mockGetSources.mockReturnValue(getSourcesPromise);

      const action = syncSources("test-token");
      const dispatchPromise = (store.dispatch as any)(action);

      // Check loading state is true while pending
      expect((store.getState() as any).sources.loading).toBe(true);
      expect((store.getState() as any).sources.error).toBeNull();

      // Resolve both promises
      resolveSyncMetadata!();
      resolveGetSources!(mockSources);
      await dispatchPromise;

      // Check loading state is false after completion
      expect((store.getState() as any).sources.loading).toBe(false);
    });

    it("fetches conversation for active source during sync", async () => {
      const activeSourceUuid = "source-1";

      // Set up store with active source
      store = configureStore({
        reducer: {
          sources: sourcesSlice,
          session: sessionSlice,
          conversation: conversationSlice,
        },
        preloadedState: {
          sources: {
            sources: [],
            activeSourceUuid: activeSourceUuid,
            loading: false,
            error: null,
            lastSyncTime: null,
          },
        },
      });

      // Mock getSourceWithItems for the active conversation
      const mockGetSourceWithItems = vi.fn();
      (window as any).electronAPI.getSourceWithItems = mockGetSourceWithItems;
      mockGetSourceWithItems.mockResolvedValue({
        uuid: activeSourceUuid,
        data: mockSources[0].data,
        items: [],
      });

      await (store.dispatch as any)(syncSources("test-token"));

      // Should have called getSourceWithItems for the active source only
      expect(mockGetSourceWithItems).toHaveBeenCalledWith(activeSourceUuid);
      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);

      // Sources should be updated
      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
    });

    it("does not fetch conversations when no active source", async () => {
      const mockGetSourceWithItems = vi.fn();
      (window as any).electronAPI.getSourceWithItems = mockGetSourceWithItems;

      await (store.dispatch as any)(syncSources("test-token"));

      // Should NOT have called getSourceWithItems since no active source
      expect(mockGetSourceWithItems).not.toHaveBeenCalled();

      // Sources should still be updated in the store
      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
    });
  });

  describe("selectors", () => {
    const mockSessionState: SessionState = {
      status: SessionStatus.Unauth,
      authData: undefined,
    };

    const mockConversationState = {
      conversation: null,
      loading: false,
      error: null,
      lastFetchTime: null,
    };

    it("selectSources returns sources array", () => {
      const state = {
        session: mockSessionState,
        sources: {
          sources: mockSources,
          activeSourceUuid: null,
          loading: false,
          error: null,
          lastSyncTime: 123456789,
        },
        conversation: mockConversationState,
      };

      expect(selectSources(state)).toEqual(mockSources);
    });

    it("selectActiveSourceUuid returns active source UUID", () => {
      const state = {
        session: mockSessionState,
        sources: {
          sources: mockSources,
          activeSourceUuid: "source-1",
          loading: false,
          error: null,
          lastSyncTime: 123456789,
        },
        conversation: mockConversationState,
      };

      expect(selectActiveSourceUuid(state)).toBe("source-1");
    });

    it("selectSourcesLoading returns loading state", () => {
      const state = {
        session: mockSessionState,
        sources: {
          sources: [],
          activeSourceUuid: null,
          loading: true,
          error: null,
          lastSyncTime: null,
        },
        conversation: mockConversationState,
      };

      expect(selectSourcesLoading(state)).toBe(true);
    });
  });

  describe("concurrent actions", () => {
    it("handles multiple fetchSources calls correctly", async () => {
      const actions = [fetchSources(), fetchSources(), fetchSources()];
      await Promise.all(
        actions.map((action) => (store.dispatch as any)(action)),
      );

      // getSources should be called 3 times
      expect(mockGetSources).toHaveBeenCalledTimes(3);

      // Final state should have sources
      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
      expect(state.loading).toBe(false);
    });

    it("handles fetchSources after syncSources", async () => {
      // First sync
      await (store.dispatch as any)(syncSources("test-token"));

      // Then fetch
      await (store.dispatch as any)(fetchSources());

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(2); // Once for sync, once for fetch

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
    });
  });

  describe("error handling edge cases", () => {
    it("handles network timeout error during sync", async () => {
      mockSyncMetadata.mockRejectedValue(new Error("Network timeout"));

      await (store.dispatch as any)(syncSources("valid-token"));

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("Network timeout");
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);

      // syncMetadata should be called but getSources should not be called due to network failure
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("handles undefined error message", async () => {
      const errorWithoutMessage = new Error();
      errorWithoutMessage.message = "";
      mockGetSources.mockRejectedValue(errorWithoutMessage);

      const action = fetchSources();
      await (store.dispatch as any)(action);

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("Failed to fetch sources");
    });

    it("handles non-Error rejection for fetchSources", async () => {
      mockGetSources.mockRejectedValue("String error");

      const action = fetchSources();
      await (store.dispatch as any)(action);

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("String error");
    });

    it("handles non-Error rejection for syncSources", async () => {
      mockSyncMetadata.mockRejectedValue("String error");

      const action = syncSources("test-token");
      await (store.dispatch as any)(action);

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("String error");
    });
  });

  describe("state transitions", () => {
    it("clears previous error when new fetch starts", async () => {
      // First, create an error state
      mockGetSources.mockRejectedValue(new Error("First error"));
      await (store.dispatch as any)(fetchSources());
      expect((store.getState() as any).sources.error).toBe("First error");

      // Then make a successful call
      mockGetSources.mockResolvedValue(mockSources);
      await (store.dispatch as any)(fetchSources());

      const state = (store.getState() as any).sources;
      expect(state.error).toBeNull();
      expect(state.sources).toEqual(mockSources);
    });

    it("updates lastSyncTime on successful operations", async () => {
      const beforeTime = Date.now();

      await (store.dispatch as any)(fetchSources());

      const afterTime = Date.now();
      const state = (store.getState() as any).sources;

      expect(state.lastSyncTime).toBeGreaterThanOrEqual(beforeTime);
      expect(state.lastSyncTime).toBeLessThanOrEqual(afterTime);
    });

    it("does not update lastSyncTime on failed operations", async () => {
      mockGetSources.mockRejectedValue(new Error("Failed"));

      await (store.dispatch as any)(fetchSources());

      const state = (store.getState() as any).sources;
      expect(state.lastSyncTime).toBeNull();
    });
  });
});
