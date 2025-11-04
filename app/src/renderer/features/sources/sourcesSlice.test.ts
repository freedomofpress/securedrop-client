/* eslint-disable @typescript-eslint/no-explicit-any */
import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import type { Source as SourceType } from "../../../types";
import sourcesSlice, {
  fetchSources,
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
      is_seen: false,
      has_attachment: false,
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
      is_seen: true,
      has_attachment: true,
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
      getSourceWithItems: vi.fn().mockResolvedValue({
        uuid: "source-1",
        data: mockSources[0].data,
        items: [],
      }),
    };

    // Default mock implementations
    mockGetSources.mockResolvedValue(mockSources);
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
      };

      const action = clearError();
      const newState = sourcesSlice(initialState, action);

      expect(newState.error).toBeNull();
      expect(newState.sources).toEqual([]);
      expect(newState.activeSourceUuid).toBeNull();
      expect(newState.loading).toBe(false);
    });
  });

  describe("setActiveSource action", () => {
    it("sets the active source UUID", () => {
      const initialState: SourcesState = {
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: null,
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
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
        conversation: mockConversationState,
        sync: {
          loading: false,
          error: null,
          lastFetchTime: null,
        },
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
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
        conversation: mockConversationState,
        sync: {
          loading: false,
          error: null,
          lastFetchTime: null,
        },
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
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
        conversation: mockConversationState,
        sync: {
          loading: false,
          error: null,
          lastFetchTime: null,
        },
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

    it("handles multiple fetchSources calls after previous actions", async () => {
      // First fetch
      await (store.dispatch as any)(fetchSources());

      // Then another fetch
      await (store.dispatch as any)(fetchSources());

      expect(mockGetSources).toHaveBeenCalledTimes(2);

      const state = (store.getState() as any).sources;
      expect(state.sources).toEqual(mockSources);
      expect(state.loading).toBe(false);
      expect(state.error).toBeNull();
    });
  });

  describe("error handling edge cases", () => {
    it("handles network timeout error during fetch", async () => {
      mockGetSources.mockRejectedValue(new Error("Network timeout"));

      await (store.dispatch as any)(fetchSources());

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("Network timeout");
      expect(state.sources).toEqual([]);
      expect(state.loading).toBe(false);

      expect(mockGetSources).toHaveBeenCalledTimes(1);
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
  });
});
