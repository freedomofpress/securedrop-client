import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import { fetchConversation } from "../conversation/conversationSlice";
import { fetchJournalists } from "../journalists/journalistsSlice";
import { fetchSources } from "../sources/sourcesSlice";

export interface SyncState {
  loading: boolean;
  error: string | null;
  lastSyncTime: number | null;
}

const initialState: SyncState = {
  loading: false,
  error: null,
  lastSyncTime: null,
};

// Async thunk for syncing metadata (sources, journalists, and active conversation)
export const syncMetadata = createAsyncThunk(
  "sync/syncMetadata",
  async (authToken: string | undefined, { getState, dispatch }) => {
    // Sync metadata with the server
    await window.electronAPI.syncMetadata({ authToken });

    // Fetch updated sources
    dispatch(fetchSources());

    // Fetch updated journalists
    dispatch(fetchJournalists());

    // Get the active source from Redux state
    const state = getState() as RootState;
    const activeSourceUuid = state.sources.activeSourceUuid;

    // If there's an active source, fetch its conversation
    if (activeSourceUuid) {
      dispatch(fetchConversation(activeSourceUuid));
    }

    return;
  },
);

export const syncSlice = createSlice({
  name: "sync",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(syncMetadata.pending, (state) => {
        state.loading = true;
        state.error = null;
      })
      .addCase(syncMetadata.fulfilled, (state) => {
        state.loading = false;
        state.lastSyncTime = Date.now();
      })
      .addCase(syncMetadata.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to sync metadata";
      });
  },
});

export const { clearError } = syncSlice.actions;
export const selectSyncLoading = (state: RootState) => state.sync.loading;
export const selectSyncError = (state: RootState) => state.sync.error;
export const selectLastSyncTime = (state: RootState) => state.sync.lastSyncTime;
export default syncSlice.reducer;
