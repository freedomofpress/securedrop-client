import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import { Item, type SourceWithItems } from "../../../types";
import type { RootState } from "../../store";
import { fetchSources } from "../sources/sourcesSlice";

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
  async (sourceUuid: string, { getState, dispatch }) => {
    const sourceWithItems =
      await window.electronAPI.getSourceWithItems(sourceUuid);

    // Read journalist UUID if auth data is available in state
    const state = getState() as RootState;
    const journalistUUID = state?.session?.authData?.journalistUUID;

    // Mark all items in this conversation as seen
    const itemUuids = sourceWithItems.items
      .filter((item) => {
        if (journalistUUID) {
          return !item.data.seen_by.includes(journalistUUID);
        } else if (item.data.kind !== "reply") {
          // Fall back to using the `is_read` field if journalist UUID is not available
          return !item.data.is_read;
        } else {
          // For replies, default to adding seen item
          return true;
        }
      })
      .map((item) => item.uuid);
    if (itemUuids.length > 0) {
      await window.electronAPI.addPendingItemsSeenBatch(sourceUuid, itemUuids);
      dispatch(fetchSources());
    }

    return { sourceUuid, sourceWithItems };
  },
);

export const updateItemFetchStatus = createAsyncThunk(
  "conversation/updateItemFetchStatus",
  async ({
    itemUuid,
    fetchStatus,
    authToken,
  }: {
    sourceUuid: string;
    itemUuid: string;
    fetchStatus: number;
    authToken: string | undefined;
  }) => {
    await window.electronAPI.updateFetchStatus(
      itemUuid,
      fetchStatus,
      authToken,
    );
    const item = await window.electronAPI.getItem(itemUuid);
    return { item };
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
    updateItem: (state, action) => {
      const updatedItem: Item = action.payload;
      if (state.conversation) {
        state.conversation.items = state.conversation.items.map((item, _) => {
          if (item.uuid === updatedItem.uuid) {
            return updatedItem;
          }
          return item;
        });
      }
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
      })
      .addCase(updateItemFetchStatus.fulfilled, (state, action) => {
        const { item: updatedItem } = action.payload;
        if (state.conversation) {
          state.conversation.items = state.conversation.items.map((item, _) => {
            if (updatedItem && item.uuid === updatedItem.uuid) {
              return updatedItem;
            }
            return item;
          });
        }
        state.lastFetchTime = Date.now();
      });
  },
});

export const { clearError, clearConversation, updateItem } =
  conversationSlice.actions;

// Selectors
export const selectConversation = (state: RootState, sourceUuid: string) =>
  state.conversation.conversation?.uuid === sourceUuid
    ? state.conversation.conversation
    : null;
export const selectConversationLoading = (state: RootState) =>
  state.conversation.loading;

export default conversationSlice.reducer;
