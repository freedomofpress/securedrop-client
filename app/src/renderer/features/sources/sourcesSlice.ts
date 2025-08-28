import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Source as SourceType } from "../../../types";
import { fetchConversation } from "../conversation/conversationSlice";

export interface SourcesState {
  sources: SourceType[];
  activeSourceUuid: string | null;
  loading: boolean;
  error: string | null;
  lastSyncTime: number | null;
}

const initialState: SourcesState = {
  sources: [],
  activeSourceUuid: null,
  loading: false,
  error: null,
  lastSyncTime: null,
};

// Async thunk for fetching sources
export const fetchSources = createAsyncThunk(
  "sources/fetchSources",
  async () => {
    const sources = await window.electronAPI.getSources();
    return sources;
  },
);

// Async thunk for syncing sources (calls sync then fetches)
export const syncSources = createAsyncThunk(
  "sources/syncSources",
  async (authToken: string | undefined, { getState, dispatch }) => {
    // Sync metadata with the server
    await window.electronAPI.syncMetadata({ authToken });

    // Fetch updated sources
    const newSources = await window.electronAPI.getSources();

    // Get the active source from Redux state
    const state = getState() as RootState;
    const activeSourceUuid = state.sources.activeSourceUuid;

    // If there's an active source, fetch its conversation
    if (activeSourceUuid) {
      dispatch(fetchConversation(activeSourceUuid));
    }

    return newSources;
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
        state.lastSyncTime = Date.now();
      })
      .addCase(fetchSources.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch sources";
      })
      // syncSources
      .addCase(syncSources.pending, (state) => {
        state.loading = true;
        state.error = null;
      })
      .addCase(syncSources.fulfilled, (state, action) => {
        state.loading = false;
        state.sources = action.payload;
        state.lastSyncTime = Date.now();
      })
      .addCase(syncSources.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to sync sources";
      });
  },
});

export const { clearError, setActiveSource, clearActiveSource } =
  sourcesSlice.actions;
export const selectSources = (state: RootState) => state.sources.sources;
export const selectActiveSourceUuid = (state: RootState) =>
  state.sources.activeSourceUuid;
export const selectSourcesLoading = (state: RootState) => state.sources.loading;
export default sourcesSlice.reducer;
