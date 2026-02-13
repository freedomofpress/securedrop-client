import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import { fetchConversation } from "../conversation/conversationSlice";
import { fetchJournalists } from "../journalists/journalistsSlice";
import { fetchSources } from "../sources/sourcesSlice";
import { SyncStatus } from "../../../types";
import type { AuthData } from "../session/sessionSlice";

export interface SyncState {
  error: string | null;
  lastSyncStarted: number | null;
  lastSyncFinished: number | null;
  status: SyncStatus | null;
}

const initialState: SyncState = {
  error: null,
  lastSyncStarted: null,
  lastSyncFinished: null,
  status: null,
};

// Async thunk for syncing metadata (sources, journalists, and active conversation)
export const syncMetadata = createAsyncThunk(
  "sync/syncMetadata",
  async (authData: AuthData, { getState, dispatch }) => {
    const hintedRecords =
      (authData.lastHintedSources || 0) + (authData.lastHintedItems || 0);

    // Only pass the hinted version (to see if we're already up to date and can
    // skip sync) if this is the very first sync after login.
    const state = getState() as RootState;
    const hintedVersion = state.sync.lastSyncStarted
      ? undefined
      : authData.lastHintedVersion;

    dispatch(markSyncStarted());

    // Sync metadata with the server
    const status: SyncStatus = await window.electronAPI.syncMetadata({
      authToken: authData.token,
      hintedRecords,
      hintedVersion,
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
    markSyncStarted: (state) => {
      state.lastSyncStarted = Date.now();
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(syncMetadata.fulfilled, (state, action) => {
        state.lastSyncFinished = Date.now();
        state.status = action.payload;
      })
      .addCase(syncMetadata.rejected, (state, action) => {
        state.error = action.error.message || "Failed to sync metadata";
      });
  },
});

export const { clearError, clearStatus, markSyncStarted } = syncSlice.actions;
export const selectSyncError = (state: RootState) => state.sync.error;
export const selectSyncStatus = (state: RootState) => state.sync.status;
export const selectLastSyncFinished = (state: RootState) =>
  state.sync.lastSyncFinished;
export default syncSlice.reducer;
