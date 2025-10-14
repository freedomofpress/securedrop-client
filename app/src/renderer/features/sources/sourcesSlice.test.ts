/* eslint-disable @typescript-eslint/no-explicit-any */
import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import type { Source as SourceType } from "../../../types";
import { PendingEventType } from "../../../types";
import sourcesSlice, {
  fetchSources,
  toggleSourceStar,
  cancelPendingSourceEvent,
  clearError,
  setActiveSource,
  clearActiveSource,
  selectSources,
  selectActiveSourceUuid,
  selectSourcesLoading,
  selectStarPendingStates,
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
        starPendingStates: {},
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
        starPendingStates: {},
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
        starPendingStates: {},
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
        starPendingStates: {},
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
          starPendingStates: {},
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
          starPendingStates: {},
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
          starPendingStates: {},
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

  describe("toggleSourceStar async thunk", () => {
    let mockAddPendingSourceEvent: ReturnType<typeof vi.fn>;

    beforeEach(() => {
      mockAddPendingSourceEvent = vi.fn();
      (window as any).electronAPI.addPendingSourceEvent =
        mockAddPendingSourceEvent;
    });

    it("handles successful star toggle (starring a source)", async () => {
      mockAddPendingSourceEvent.mockResolvedValue(BigInt(12345));

      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      expect(mockAddPendingSourceEvent).toHaveBeenCalledWith(
        "source-1",
        PendingEventType.Starred,
      );

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toEqual({
        targetStarState: true,
        snowflakeId: "12345",
      });
      expect(state.error).toBeNull();
    });

    it("handles successful star toggle (unstarring a source)", async () => {
      mockAddPendingSourceEvent.mockResolvedValue(BigInt(67890));

      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-2", targetStarState: false }),
      );

      expect(mockAddPendingSourceEvent).toHaveBeenCalledWith(
        "source-2",
        PendingEventType.Unstarred,
      );

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-2"]).toEqual({
        targetStarState: false,
        snowflakeId: "67890",
      });
    });

    it("sets pending state immediately when toggleSourceStar is dispatched", async () => {
      let resolveAddPendingEvent!: (value: bigint) => void;
      const addPendingPromise = new Promise<bigint>((resolve) => {
        resolveAddPendingEvent = resolve;
      });
      mockAddPendingSourceEvent.mockReturnValue(addPendingPromise);

      const action = toggleSourceStar({
        sourceUuid: "source-1",
        targetStarState: true,
      });
      const dispatchPromise = (store.dispatch as any)(action);

      // Check pending state is set immediately (with empty snowflakeId)
      const pendingState = (store.getState() as any).sources.starPendingStates[
        "source-1"
      ];
      expect(pendingState).toEqual({
        targetStarState: true,
        snowflakeId: "",
      });

      // Resolve and check snowflakeId is populated
      resolveAddPendingEvent!(BigInt(99999));
      await dispatchPromise;

      const fulfilledState = (store.getState() as any).sources
        .starPendingStates["source-1"];
      expect(fulfilledState).toEqual({
        targetStarState: true,
        snowflakeId: "99999",
      });
    });

    it("removes pending state on toggleSourceStar failure", async () => {
      const errorMessage = "Failed to add pending event";
      mockAddPendingSourceEvent.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toBeUndefined();
      expect(state.error).toBe(errorMessage);
    });

    it("handles multiple star toggles for different sources", async () => {
      mockAddPendingSourceEvent
        .mockResolvedValueOnce(BigInt(111))
        .mockResolvedValueOnce(BigInt(222));

      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-2", targetStarState: false }),
      );

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toEqual({
        targetStarState: true,
        snowflakeId: "111",
      });
      expect(state.starPendingStates["source-2"]).toEqual({
        targetStarState: false,
        snowflakeId: "222",
      });
    });

    it("allows canceling and re-toggling a source star", async () => {
      mockAddPendingSourceEvent
        .mockResolvedValueOnce(BigInt(111))
        .mockResolvedValueOnce(BigInt(222));
      const mockRemovePendingEvent = vi.fn().mockResolvedValue(undefined);
      (window as any).electronAPI.removePendingEvent = mockRemovePendingEvent;

      // First toggle - creates pending state
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      let state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toEqual({
        targetStarState: true,
        snowflakeId: "111",
      });

      // Cancel the pending state
      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-1",
          snowflakeId: "111",
        }),
      );

      state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toBeUndefined();

      // Now can toggle again in the opposite direction
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: false }),
      );

      state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toEqual({
        targetStarState: false,
        snowflakeId: "222",
      });
    });

    it("handles error with undefined message in toggleSourceStar", async () => {
      const errorWithoutMessage = new Error();
      errorWithoutMessage.message = "";
      mockAddPendingSourceEvent.mockRejectedValue(errorWithoutMessage);

      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("Failed to toggle star");
      expect(state.starPendingStates["source-1"]).toBeUndefined();
    });
  });

  describe("cancelPendingSourceEvent async thunk", () => {
    let mockRemovePendingEvent: ReturnType<typeof vi.fn>;
    let mockAddPendingSourceEvent: ReturnType<typeof vi.fn>;

    beforeEach(() => {
      mockRemovePendingEvent = vi.fn();
      mockAddPendingSourceEvent = vi.fn();
      (window as any).electronAPI.removePendingEvent = mockRemovePendingEvent;
      (window as any).electronAPI.addPendingSourceEvent =
        mockAddPendingSourceEvent;
    });

    it("removes pending state when event is successfully canceled", async () => {
      mockRemovePendingEvent.mockResolvedValue(undefined);
      mockAddPendingSourceEvent.mockResolvedValue(BigInt(12345));

      // First add a pending state
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      expect(
        (store.getState() as any).sources.starPendingStates["source-1"],
      ).toBeDefined();

      // Then cancel it
      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-1",
          snowflakeId: "12345",
        }),
      );

      expect(mockRemovePendingEvent).toHaveBeenCalledWith(BigInt(12345));

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toBeUndefined();
      expect(state.error).toBeNull();
    });

    it("handles cancelPendingSourceEvent failure", async () => {
      const errorMessage = "Failed to remove pending event";
      mockRemovePendingEvent.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-1",
          snowflakeId: "12345",
        }),
      );

      const state = (store.getState() as any).sources;
      expect(state.error).toBe(errorMessage);
    });

    it("handles canceling non-existent pending state gracefully", async () => {
      mockRemovePendingEvent.mockResolvedValue(undefined);

      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-999",
          snowflakeId: "99999",
        }),
      );

      expect(mockRemovePendingEvent).toHaveBeenCalledWith(BigInt(99999));

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-999"]).toBeUndefined();
      expect(state.error).toBeNull();
    });

    it("handles error with undefined message in cancelPendingSourceEvent", async () => {
      const errorWithoutMessage = new Error();
      errorWithoutMessage.message = "";
      mockRemovePendingEvent.mockRejectedValue(errorWithoutMessage);

      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-1",
          snowflakeId: "12345",
        }),
      );

      const state = (store.getState() as any).sources;
      expect(state.error).toBe("Failed to cancel pending event");
    });
  });

  describe("pending states interaction with fetchSources", () => {
    let mockAddPendingSourceEvent: ReturnType<typeof vi.fn>;

    beforeEach(() => {
      mockAddPendingSourceEvent = vi.fn();
      (window as any).electronAPI.addPendingSourceEvent =
        mockAddPendingSourceEvent;
    });

    it("clears all pending star states when sources are successfully fetched", async () => {
      mockAddPendingSourceEvent.mockResolvedValue(BigInt(12345));

      // Add some pending states
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-2", targetStarState: false }),
      );

      let state = (store.getState() as any).sources;
      expect(Object.keys(state.starPendingStates).length).toBe(2);

      // Fetch sources should clear pending states
      await (store.dispatch as any)(fetchSources());

      state = (store.getState() as any).sources;
      expect(state.starPendingStates).toEqual({});
      expect(state.sources).toEqual(mockSources);
    });

    it("does not clear pending states when fetchSources fails", async () => {
      mockAddPendingSourceEvent.mockResolvedValue(BigInt(12345));

      // Add a pending state
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      // Make fetchSources fail
      mockGetSources.mockRejectedValue(new Error("Network error"));
      await (store.dispatch as any)(fetchSources());

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toBeDefined();
      expect(state.error).toBe("Network error");
    });
  });

  describe("selectStarPendingStates selector", () => {
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

    it("returns empty object when no pending states exist", () => {
      const state = {
        session: mockSessionState,
        sources: {
          sources: [],
          activeSourceUuid: null,
          loading: false,
          error: null,
          starPendingStates: {},
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

      expect(selectStarPendingStates(state)).toEqual({});
    });

    it("returns pending states when they exist", () => {
      const pendingStates = {
        "source-1": { targetStarState: true, snowflakeId: "12345" },
        "source-2": { targetStarState: false, snowflakeId: "67890" },
      };

      const state = {
        session: mockSessionState,
        sources: {
          sources: [],
          activeSourceUuid: null,
          loading: false,
          error: null,
          starPendingStates: pendingStates,
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

      expect(selectStarPendingStates(state)).toEqual(pendingStates);
    });
  });

  describe("edge cases for pending states", () => {
    it("handles rapid toggle and cancel operations", async () => {
      const mockAddPendingSourceEvent = vi
        .fn()
        .mockResolvedValue(BigInt(12345));
      const mockRemovePendingEvent = vi.fn().mockResolvedValue(undefined);
      (window as any).electronAPI.addPendingSourceEvent =
        mockAddPendingSourceEvent;
      (window as any).electronAPI.removePendingEvent = mockRemovePendingEvent;

      // Toggle
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: true }),
      );

      // Cancel
      await (store.dispatch as any)(
        cancelPendingSourceEvent({
          sourceUuid: "source-1",
          snowflakeId: "12345",
        }),
      );

      // Toggle again
      await (store.dispatch as any)(
        toggleSourceStar({ sourceUuid: "source-1", targetStarState: false }),
      );

      const state = (store.getState() as any).sources;
      expect(state.starPendingStates["source-1"]).toEqual({
        targetStarState: false,
        snowflakeId: "12345",
      });
    });
  });
});
