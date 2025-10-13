import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Source as SourceType } from "../../../types";
import { PendingEventType } from "../../../types";

export interface SourcesState {
  sources: SourceType[];
  activeSourceUuid: string | null;
  loading: boolean;
  error: string | null;
  starPendingStates: { [sourceUuid: string]: boolean };
}

const initialState: SourcesState = {
  sources: [],
  activeSourceUuid: null,
  loading: false,
  error: null,
  starPendingStates: {},
};

// Async thunk for fetching sources
export const fetchSources = createAsyncThunk(
  "sources/fetchSources",
  async () => {
    const sources = await window.electronAPI.getSources();
    return sources;
  },
);

// Async thunk for toggling source star
export const toggleSourceStar = createAsyncThunk(
  "sources/toggleSourceStar",
  async ({
    sourceUuid,
    targetStarState,
  }: {
    sourceUuid: string;
    targetStarState: boolean;
  }) => {
    const eventType = targetStarState
      ? PendingEventType.Starred
      : PendingEventType.Unstarred;
    const snowflakeId = await window.electronAPI.addPendingSourceEvent(
      sourceUuid,
      eventType,
    );
    return { sourceUuid, targetStarState, snowflakeId };
  },
);

export const sourcesSlice = createSlice({
  name: "sources",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
    setActiveSource: (state, action) => {
      state.activeSourceUuid = action.payload;
    },
    clearActiveSource: (state) => {
      state.activeSourceUuid = null;
    },
  },
  extraReducers: (builder) => {
    builder
      // fetchSources
      .addCase(fetchSources.pending, (state) => {
        state.loading = true;
        state.error = null;
      })
      .addCase(fetchSources.fulfilled, (state, action) => {
        state.loading = false;
        state.sources = action.payload;
        // Clear all pending star states when sources are synced
        state.starPendingStates = {};
      })
      .addCase(fetchSources.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch sources";
      })
      // toggleSourceStar
      .addCase(toggleSourceStar.pending, (state, action) => {
        const { sourceUuid, targetStarState } = action.meta.arg;
        state.starPendingStates[sourceUuid] = targetStarState;
      })
      .addCase(toggleSourceStar.fulfilled, (state, action) => {
        // Keep the pending state - it will be cleared on next sync
        const { sourceUuid, targetStarState } = action.payload;
        state.starPendingStates[sourceUuid] = targetStarState;
      })
      .addCase(toggleSourceStar.rejected, (state, action) => {
        const { sourceUuid } = action.meta.arg;
        // Remove pending state on failure to revert to original
        delete state.starPendingStates[sourceUuid];
        state.error = action.error.message || "Failed to toggle star";
      });
  },
});

export const { clearError, setActiveSource, clearActiveSource } =
  sourcesSlice.actions;
export const selectSources = (state: RootState) => state.sources.sources;
export const selectActiveSourceUuid = (state: RootState) =>
  state.sources.activeSourceUuid;
export const selectSourcesLoading = (state: RootState) => state.sources.loading;
export const selectStarPendingStates = (state: RootState) =>
  state.sources.starPendingStates;
export default sourcesSlice.reducer;
