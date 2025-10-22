import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import { fetchConversation } from "../conversation/conversationSlice";
import { fetchJournalists } from "../journalists/journalistsSlice";
import { fetchSources } from "../sources/sourcesSlice";
import { SyncStatus } from "../../../types";

export interface SyncState {
  error: string | null;
  lastFetchTime: number | null;
}

const initialState: SyncState = {
  error: null,
  lastFetchTime: null,
};

// Async thunk for syncing metadata (sources, journalists, and active conversation)
export const syncMetadata = createAsyncThunk(
  "sync/syncMetadata",
  async (authToken: string | undefined, { getState, dispatch }) => {
    // Sync metadata with the server
    const status: SyncStatus = await window.electronAPI.syncMetadata({
      authToken,
    });

    // If there are updates from sync, fetch downstream state
    if (status === SyncStatus.UPDATED) {
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
      .addCase(syncMetadata.fulfilled, (state) => {
        state.lastFetchTime = Date.now();
      })
      .addCase(syncMetadata.rejected, (state, action) => {
        state.error = action.error.message || "Failed to sync metadata";
      });
  },
});

export const { clearError } = syncSlice.actions;
export const selectSyncError = (state: RootState) => state.sync.error;
export const selectlastFetchTime = (state: RootState) =>
  state.sync.lastFetchTime;
export default syncSlice.reducer;
