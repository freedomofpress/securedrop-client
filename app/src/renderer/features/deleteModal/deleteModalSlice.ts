import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { RootState } from "../../store";
import { setUnauth } from "../session/sessionSlice";

export interface DeleteItemCounts {
  messages: number;
  files: number;
  replies: number;
}

export interface DeleteModalState {
  open: boolean;
  // UUIDs of the sources targeted for deletion.
  pendingSources: string[];
  // True while the per-source item counts are being fetched.
  loading: boolean;
  counts: DeleteItemCounts;
  // UUIDs acted on by the most recent completed deletion. The source list drops
  // these from its checkbox selection. Needed because the visibility-based
  // selection pruning only clears sources that leave the store, so it misses
  // the "delete conversation" (truncate) case, where the source stays.
  lastDeletedSources: string[];
}

const emptyCounts: DeleteItemCounts = { messages: 0, files: 0, replies: 0 };

const initialState: DeleteModalState = {
  open: false,
  pendingSources: [],
  loading: false,
  counts: emptyCounts,
  lastDeletedSources: [],
};

// Opens the delete confirmation modal for the given sources and fetches the
// number of messages, files and replies that would be affected. The single
// entry point used by every caller (source list, source menu, keyboard
// shortcut) so the modal exists once at the top of the tree.
export const openDeleteModal = createAsyncThunk(
  "deleteModal/open",
  async (sources: string[]) => {
    return await window.electronAPI.getSourceItemCounts(sources);
  },
  {
    // Ignore requests with no sources selected.
    condition: (sources) => sources.length > 0,
  },
);

export const deleteModalSlice = createSlice({
  name: "deleteModal",
  initialState,
  reducers: {
    // Cancel: reset everything, and (via the stable initialState reference)
    // leave no completion signal for the source list to act on.
    closeDeleteModal: () => initialState,
    // Success: close the modal and record the acted-on sources so the source
    // list can drop them from its checkbox selection. A fresh array is used so
    // each completion is a distinct reference.
    completeDeleteModal: (state) => ({
      ...initialState,
      lastDeletedSources: [...state.pendingSources],
    }),
  },
  extraReducers: (builder) => {
    builder
      // Drop any in-flight delete confirmation when the session ends, so a
      // modal left open at logout (e.g. a 403 during sync) doesn't reappear —
      // referencing stale sources — on the next login.
      .addCase(setUnauth.fulfilled, () => initialState)
      .addCase(openDeleteModal.pending, (state, action) => {
        state.open = true;
        state.loading = true;
        state.pendingSources = action.meta.arg;
        state.counts = emptyCounts;
      })
      .addCase(openDeleteModal.fulfilled, (state, action) => {
        state.loading = false;
        state.counts = action.payload;
      })
      .addCase(openDeleteModal.rejected, (state) => {
        state.loading = false;
        state.counts = emptyCounts;
      });
  },
});

export const { closeDeleteModal, completeDeleteModal } =
  deleteModalSlice.actions;

export const selectDeleteModal = (state: RootState) => state.deleteModal;
export const selectDeleteModalOpen = (state: RootState) =>
  state.deleteModal.open;
export const selectLastDeletedSources = (state: RootState) =>
  state.deleteModal.lastDeletedSources;

export default deleteModalSlice.reducer;
