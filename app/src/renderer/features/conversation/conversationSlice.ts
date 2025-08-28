import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import type { SourceWithItems } from "../../../types";
import type { RootState } from "../../store";

export interface ConversationState {
  conversation: SourceWithItems | null;
  loading: boolean;
  error: string | null;
  lastFetchTime: number | null;
}

const initialState: ConversationState = {
  conversation: null,
  loading: false,
  error: null,
  lastFetchTime: null,
};

export const fetchConversation = createAsyncThunk(
  "conversation/fetchConversation",
  async (sourceUuid: string) => {
    const sourceWithItems =
      await window.electronAPI.getSourceWithItems(sourceUuid);
    return { sourceUuid, sourceWithItems };
  },
);

const conversationSlice = createSlice({
  name: "conversation",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
    clearConversation: (state) => {
      state.conversation = null;
      state.lastFetchTime = null;
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(fetchConversation.pending, (state) => {
        state.loading = true;
        state.error = null;
      })
      .addCase(fetchConversation.fulfilled, (state, action) => {
        state.loading = false;
        state.error = null;
        const { sourceWithItems } = action.payload;
        state.conversation = sourceWithItems;
        state.lastFetchTime = Date.now();
      })
      .addCase(fetchConversation.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch conversation";
      });
  },
});

export const { clearError, clearConversation } = conversationSlice.actions;

// Selectors
export const selectConversation = (state: RootState, sourceUuid: string) =>
  state.conversation.conversation?.uuid === sourceUuid
    ? state.conversation.conversation
    : null;
export const selectConversationLoading = (state: RootState) =>
  state.conversation.loading;

export default conversationSlice.reducer;
