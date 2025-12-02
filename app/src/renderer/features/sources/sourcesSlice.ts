import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Source as SourceType } from "../../../types";

export interface ConversationIndicatorState {
  lastSeenInteractionCount: number | null;
}

export interface SourcesState {
  sources: SourceType[];
  activeSourceUuid: string | null;
  loading: boolean;
  error: string | null;
  conversationIndicators: Record<string, ConversationIndicatorState>;
}

const initialState: SourcesState = {
  sources: [],
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
      state.sources = state.sources.map((source, _) => {
        if (source.uuid === updatedSource.uuid) {
          return updatedSource;
        }
        return source;
      });
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
        state.sources = action.payload;

        // Update active source UUID in case of deletion
        if (!state.sources.find((s) => s.uuid === state.activeSourceUuid)) {
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
export const selectSources = (state: RootState) => state.sources.sources;
export const selectActiveSourceUuid = (state: RootState) =>
  state.sources.activeSourceUuid;
export const selectSourcesLoading = (state: RootState) => state.sources.loading;
export const selectConversationLastSeen = (
  state: RootState,
  sourceUuid: string,
) => state.sources.conversationIndicators[sourceUuid]?.lastSeenInteractionCount;
export default sourcesSlice.reducer;
