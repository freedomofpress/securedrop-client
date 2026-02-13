import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import { fetchConversation } from "../conversation/conversationSlice";
import { fetchJournalists } from "../journalists/journalistsSlice";
import { fetchSources } from "../sources/sourcesSlice";
import { SyncStatus } from "../../../types";
import type { AuthData } from "../session/sessionSlice";

export interface SyncState {
  error: string | null;
  lastFetchTime: number | null;
  status: SyncStatus | null;
}

const initialState: SyncState = {
  error: null,
  lastFetchTime: null,
  status: null,
};

// Async thunk for syncing metadata (sources, journalists, and active conversation)
export const syncMetadata = createAsyncThunk(
  "sync/syncMetadata",
  async (authData: AuthData, { getState, dispatch }) => {
    const hintedRecords =
      (authData.lastHintedSources || 0) + (authData.lastHintedItems || 0);
    // Sync metadata with the server
    const status: SyncStatus = await window.electronAPI.syncMetadata({
      authToken: authData.token,
      hintedRecords,
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

    return status;
  },
);

export const syncSlice = createSlice({
  name: "sync",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
    clearStatus: (state) => {
      state.status = null;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(syncMetadata.fulfilled, (state, action) => {
        state.lastFetchTime = Date.now();
        state.status = action.payload;
      })
      .addCase(syncMetadata.rejected, (state, action) => {
        state.error = action.error.message || "Failed to sync metadata";
      });
  },
});

export const { clearError, clearStatus } = syncSlice.actions;
export const selectSyncError = (state: RootState) => state.sync.error;
export const selectSyncStatus = (state: RootState) => state.sync.status;
export const selectlastFetchTime = (state: RootState) =>
  state.sync.lastFetchTime;
export default syncSlice.reducer;
