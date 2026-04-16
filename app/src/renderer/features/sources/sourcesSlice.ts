import { createSlice, createAsyncThunk, createSelector } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Source as SourceType } from "../../../types";

export interface ConversationIndicatorState {
  lastSeenInteractionCount: number | null;
}

export interface SourcesState {
  sources: Record<string, SourceType>;
  sourceIds: string[];
  activeSourceUuid: string | null;
  loading: boolean;
  error: string | null;
  conversationIndicators: Record<string, ConversationIndicatorState>;
}

const initialState: SourcesState = {
  sources: {},
  sourceIds: [],
  activeSourceUuid: null,
  loading: false,
  error: null,
  conversationIndicators: {},
};

// Async thunk for fetching sources
export const fetchSources = createAsyncThunk(
  "sources/fetchSources",
  async () => {
    const sources = await window.electronAPI.getSources();
    return sources;
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
    updateSource: (state, action) => {
      const updatedSource: SourceType = action.payload;
      state.sources[updatedSource.uuid] = updatedSource;
    },
    initializeConversationIndicator: (state, action) => {
      const { sourceUuid, lastSeenInteractionCount } = action.payload;
      if (!state.conversationIndicators[sourceUuid]) {
        state.conversationIndicators[sourceUuid] = {
          lastSeenInteractionCount: lastSeenInteractionCount ?? null,
        };
      }
    },
    markConversationLastSeen: (state, action) => {
      const { sourceUuid, interactionCount } = action.payload;
      state.conversationIndicators[sourceUuid] = {
        lastSeenInteractionCount: interactionCount ?? null,
      };
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
        state.sources = Object.fromEntries(
          action.payload.map((s) => [s.uuid, s]),
        );
        state.sourceIds = action.payload.map((s) => s.uuid);

        // Update active source UUID in case of deletion
        if (state.activeSourceUuid && !state.sources[state.activeSourceUuid]) {
          state.activeSourceUuid = null;
        }
      })
      .addCase(fetchSources.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch sources";
      });
  },
});

export const {
  clearError,
  setActiveSource,
  clearActiveSource,
  updateSource,
  initializeConversationIndicator,
  markConversationLastSeen,
} = sourcesSlice.actions;
// selectSourceIds is stable across per-source data updates (updateSource
// only modifies sources[uuid], not sourceIds). Consumers that only need the
// ordered list of IDs — e.g. to render list structure while each row selects
// its own source — should prefer selectSourceIds over selectSources.
export const selectSourceIds = (state: RootState) => state.sources.sourceIds;
const selectSourcesById = (state: RootState) => state.sources.sources;
export const selectSources = createSelector(
  selectSourceIds,
  selectSourcesById,
  (ids, byId) => ids.map((id) => byId[id]).filter(Boolean) as SourceType[],
);
export const selectActiveSourceUuid = (state: RootState) =>
  state.sources.activeSourceUuid;
export const selectSourcesLoading = (state: RootState) => state.sources.loading;
export const selectConversationLastSeen = (
  state: RootState,
  sourceUuid: string,
) => state.sources.conversationIndicators[sourceUuid]?.lastSeenInteractionCount;
export default sourcesSlice.reducer;
