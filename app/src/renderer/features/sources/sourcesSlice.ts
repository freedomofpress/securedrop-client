import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import type { Source as SourceType } from "../../../types";

export interface SourcesState {
  sources: SourceType[];
  activeSourceUuid: string | null;
  loading: boolean;
  error: string | null;
}

const initialState: SourcesState = {
  sources: [],
  activeSourceUuid: null,
  loading: false,
  error: null,
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
      })
      .addCase(fetchSources.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch sources";
      });
  },
});

export const { clearError, setActiveSource, clearActiveSource, updateSource } =
  sourcesSlice.actions;
export const selectSources = (state: RootState) => state.sources.sources;
export const selectActiveSourceUuid = (state: RootState) =>
  state.sources.activeSourceUuid;
export const selectSourcesLoading = (state: RootState) => state.sources.loading;
export default sourcesSlice.reducer;
