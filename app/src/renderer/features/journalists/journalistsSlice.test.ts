import { describe, it, expect, vi, beforeEach } from "vitest";
import { configureStore, type EnhancedStore } from "@reduxjs/toolkit";
import type { Journalist } from "../../../types";
import journalistsReducer, {
  fetchJournalists,
  clearError,
  getJournalistsState,
  getJournalists,
  getJournalistsLoading,
  getJournalistsError,
  type JournalistsState,
} from "./journalistsSlice";

// Mock electronAPI
const mockElectronAPI = {
  getJournalists: vi.fn(),
};

// Set up window.electronAPI mock
Object.defineProperty(window, "electronAPI", {
  value: mockElectronAPI,
  writable: true,
});

describe("journalistsSlice", () => {
  const mockJournalists: Journalist[] = [
    {
      uuid: "journalist-1",
      data: {
        uuid: "journalist-1",
        username: "journalist",
        first_name: null,
        last_name: null,
      },
    },
    {
      uuid: "journalist-2",
      data: {
        uuid: "journalist-2",
        username: "dellsberg",
        first_name: "Daniel",
        last_name: "Ellsberg",
      },
    },
    {
      uuid: "journalist-3",
      data: {
        uuid: "journalist-3",
        username: "deleted",
        first_name: null,
        last_name: null,
      },
    },
  ];

  const initialState: JournalistsState = {
    journalists: [],
    loading: false,
    error: null,
  };

  const loadingState: JournalistsState = {
    journalists: [],
    loading: true,
    error: null,
  };

  const loadedState: JournalistsState = {
    journalists: mockJournalists,
    loading: false,
    error: null,
  };

  const errorState: JournalistsState = {
    journalists: [],
    loading: false,
    error: "Failed to fetch journalists",
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it("should have the correct initial state", () => {
    const result = journalistsReducer(undefined, { type: "unknown" });
    expect(result).toEqual(initialState);
  });

  describe("clearError action", () => {
    it("should clear the error state", () => {
      const result = journalistsReducer(errorState, clearError());
      expect(result).toEqual({
        ...errorState,
        error: null,
      });
    });

    it("should not change state when no error exists", () => {
      const result = journalistsReducer(initialState, clearError());
      expect(result).toEqual(initialState);
    });
  });

  describe("fetchJournalists async thunk", () => {
    let store: EnhancedStore<{
      journalists: JournalistsState;
    }>;

    beforeEach(() => {
      store = configureStore({
        reducer: {
          journalists: journalistsReducer,
        },
      });
    });

    it("should handle pending state", () => {
      const action = { type: fetchJournalists.pending.type };
      const result = journalistsReducer(initialState, action);

      expect(result).toEqual({
        journalists: [],
        loading: true,
        error: null,
      });
    });

    it("should handle fulfilled state", () => {
      const action = {
        type: fetchJournalists.fulfilled.type,
        payload: mockJournalists,
      };
      const result = journalistsReducer(loadingState, action);

      expect(result).toEqual({
        journalists: mockJournalists,
        loading: false,
        error: null,
      });
    });

    it("should handle rejected state", () => {
      const errorMessage = "Error";
      const action = {
        type: fetchJournalists.rejected.type,
        error: { message: errorMessage },
      };
      const result = journalistsReducer(loadingState, action);

      expect(result).toEqual({
        journalists: [],
        loading: false,
        error: errorMessage,
      });
    });

    it("should handle rejected state with default error message", () => {
      const action = {
        type: fetchJournalists.rejected.type,
        error: {},
      };
      const result = journalistsReducer(loadingState, action);

      expect(result).toEqual({
        journalists: [],
        loading: false,
        error: "Failed to fetch journalists",
      });
    });

    it("should call electronAPI.getJournalists when dispatched", async () => {
      mockElectronAPI.getJournalists.mockResolvedValue(mockJournalists);

      const thunk = fetchJournalists();
      const result = await thunk(store.dispatch, store.getState, undefined);

      expect(mockElectronAPI.getJournalists).toHaveBeenCalledTimes(1);
      expect(result.type).toBe("journalists/fetchJournalists/fulfilled");
      expect(result.payload).toEqual(mockJournalists);
    });

    it("should handle electronAPI rejection", async () => {
      const errorMessage = "IPC call failed";
      mockElectronAPI.getJournalists.mockRejectedValue(new Error(errorMessage));

      const thunk = fetchJournalists();
      const result = await thunk(store.dispatch, store.getState, undefined);

      expect(mockElectronAPI.getJournalists).toHaveBeenCalledTimes(1);
      expect(result.type).toBe("journalists/fetchJournalists/rejected");
      if (fetchJournalists.rejected.match(result)) {
        expect(result.error?.message).toBe(errorMessage);
      }
    });
  });

  describe("selectors", () => {
    const mockRootState = {
      journalists: loadedState,
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      session: {} as any, // Mock other state slices
      sources: {
        sources: [],
        activeSourceUuid: null,
        loading: false,
        error: null,
        lastSyncTime: null,
      },
      conversation: {
        conversation: null,
        loading: false,
        error: null,
        lastFetchTime: null,
      },
    };

    it("getJournalistsState should return the entire journalists state", () => {
      const result = getJournalistsState(mockRootState);
      expect(result).toEqual(loadedState);
    });

    it("getJournalists should return the journalists array", () => {
      const result = getJournalists(mockRootState);
      expect(result).toEqual(mockJournalists);
    });

    it("getJournalistsLoading should return the loading state", () => {
      const loadingRootState = {
        ...mockRootState,
        journalists: loadingState,
      };
      const result = getJournalistsLoading(loadingRootState);
      expect(result).toBe(true);
    });

    it("getJournalistsError should return the error state", () => {
      const errorRootState = {
        ...mockRootState,
        journalists: errorState,
      };
      const result = getJournalistsError(errorRootState);
      expect(result).toBe("Failed to fetch journalists");
    });

    it("getJournalistsError should return null when no error", () => {
      const result = getJournalistsError(mockRootState);
      expect(result).toBeNull();
    });
  });

  describe("edge cases", () => {
    it("should handle empty journalists array", () => {
      const action = {
        type: fetchJournalists.fulfilled.type,
        payload: [],
      };
      const result = journalistsReducer(loadingState, action);

      expect(result.journalists).toEqual([]);
      expect(result.loading).toBe(false);
      expect(result.error).toBeNull();
    });

    it("should preserve existing journalists when starting new fetch", () => {
      const result = journalistsReducer(loadedState, {
        type: fetchJournalists.pending.type,
      });

      expect(result.journalists).toEqual(mockJournalists);
      expect(result.loading).toBe(true);
      expect(result.error).toBeNull();
    });

    it("should replace existing journalists with new data", () => {
      const newJournalists: Journalist[] = [
        {
          uuid: "new-journalist",
          data: {
            uuid: "new-journalist",
            username: "newuser",
            first_name: "New",
            last_name: "User",
          },
        },
      ];

      const result = journalistsReducer(loadedState, {
        type: fetchJournalists.fulfilled.type,
        payload: newJournalists,
      });

      expect(result.journalists).toEqual(newJournalists);
      expect(result.journalists).not.toEqual(mockJournalists);
    });
  });
});
