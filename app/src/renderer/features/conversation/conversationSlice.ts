import { createSlice, createAsyncThunk } from "@reduxjs/toolkit";
import {
  Item,
  NONPROCESSABLE_FETCH_STATUSES,
  type SourceWithItems,
} from "../../../types";
import type { RootState } from "../../store";
import { fetchSources } from "../sources/sourcesSlice";

export interface ConversationState {
  conversation: SourceWithItems | null;
  loading: boolean;
  error: string | null;
  lastFetchTime: number | null;
  hasMoreHistoricalItems: boolean;
  olderItemsLoading: boolean;
}

const initialState: ConversationState = {
  conversation: null,
  loading: false,
  error: null,
  lastFetchTime: null,
  hasMoreHistoricalItems: false,
  olderItemsLoading: false,
};

const CONVERSATION_PAGE_SIZE = 100;

export const fetchConversation = createAsyncThunk(
  "conversation/fetchConversation",
  async (sourceUuid: string, { dispatch }) => {
    const sourceWithItems = await window.electronAPI.getSourceWithItems(
      sourceUuid,
      { limit: CONVERSATION_PAGE_SIZE },
    );

    // Mark all items in this conversation as seen
    const maxInteractionCount = sourceWithItems.items.reduce(
      (max, item) => Math.max(max, item.data.interaction_count ?? 0),
      0,
    );
    if (maxInteractionCount > 0) {
      const created = await window.electronAPI.addPendingSourceConversationSeen(
        sourceUuid,
        maxInteractionCount,
      );
      if (created) {
        dispatch(fetchSources());
      }
    }

    return { sourceUuid, sourceWithItems };
  },
);

export const fetchOlderConversationItems = createAsyncThunk(
  "conversation/fetchOlderConversationItems",
  async (sourceUuid: string, { getState, dispatch }) => {
    const state = getState() as RootState;
    const conversation = state.conversation.conversation;
    if (!conversation || conversation.uuid !== sourceUuid) {
      return null;
    }

    const oldestItem = conversation.items[0];
    const beforeInteractionCount = oldestItem?.data.interaction_count;

    const sourceWithItems = await window.electronAPI.getSourceWithItems(
      sourceUuid,
      { limit: CONVERSATION_PAGE_SIZE, beforeInteractionCount },
    );

    // Mark all older items in this conversation as seen
    const maxInteractionCount = sourceWithItems.items.reduce(
      (max, item) => Math.max(max, item.data.interaction_count ?? 0),
      0,
    );
    if (maxInteractionCount > 0) {
      const created = await window.electronAPI.addPendingSourceConversationSeen(
        sourceUuid,
        maxInteractionCount,
      );
      if (created) {
        dispatch(fetchSources());
      }
    }

    return sourceWithItems;
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
      state.hasMoreHistoricalItems = false;
      state.olderItemsLoading = false;
    },
    updateItem: (state, action) => {
      const updatedItem: Item = action.payload;
      if (state.conversation) {
        state.conversation.items = state.conversation.items.map((item) => {
          if (item.uuid !== updatedItem.uuid) {
            return item;
          }

          // Check that the update does not transition from a terminal state, indicating
          // a stale update. If so, ignore.

          if (
            item.fetch_status &&
            NONPROCESSABLE_FETCH_STATUSES.has(item.fetch_status)
          ) {
            return item;
          }

          return updatedItem;
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
        state.hasMoreHistoricalItems =
          sourceWithItems.hasMoreHistoricalItems ?? false;
        state.lastFetchTime = Date.now();
      })
      .addCase(fetchConversation.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to fetch conversation";
      })
      .addCase(fetchOlderConversationItems.pending, (state) => {
        state.olderItemsLoading = true;
      })
      .addCase(fetchOlderConversationItems.fulfilled, (state, action) => {
        state.olderItemsLoading = false;
        if (!action.payload || !state.conversation) {
          return;
        }
        const { items, hasMoreHistoricalItems } = action.payload;
        const existingUuids = new Set(
          state.conversation.items.map((i) => i.uuid),
        );
        const olderItems = items.filter((i) => !existingUuids.has(i.uuid));
        state.conversation.items = [...olderItems, ...state.conversation.items];
        state.hasMoreHistoricalItems = hasMoreHistoricalItems ?? false;
      })
      .addCase(fetchOlderConversationItems.rejected, (state) => {
        state.olderItemsLoading = false;
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
export const selectLastConversation = (state: RootState) =>
  state.conversation.conversation;
export const selectConversationLoading = (state: RootState) =>
  state.conversation.loading;
export const selectHasMoreHistoricalItems = (state: RootState) =>
  state.conversation.hasMoreHistoricalItems;
export const selectOlderItemsLoading = (state: RootState) =>
  state.conversation.olderItemsLoading;

export default conversationSlice.reducer;
