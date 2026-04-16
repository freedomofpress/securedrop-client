import {
  createSlice,
  createAsyncThunk,
  createSelector,
} from "@reduxjs/toolkit";
import { Item, type SourceWithItems } from "../../../types";
import type { RootState } from "../../store";
import { fetchSources } from "../sources/sourcesSlice";

export interface ConversationState {
  sourceMetadata: Omit<SourceWithItems, "items"> | null;
  itemsById: Record<string, Item>;
  loading: boolean;
  error: string | null;
  lastFetchTime: number | null;
  hasMoreHistoricalItems: boolean;
  olderItemsLoading: boolean;
}

const initialState: ConversationState = {
  sourceMetadata: null,
  itemsById: {},
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
    const { sourceMetadata, itemsById } = state.conversation;
    if (!sourceMetadata || sourceMetadata.uuid !== sourceUuid) {
      return null;
    }

    const oldestItem = Object.values(itemsById)[0];
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
      state.sourceMetadata = null;
      state.itemsById = {};
      state.lastFetchTime = null;
      state.hasMoreHistoricalItems = false;
      state.olderItemsLoading = false;
    },
    updateItem: (state, action) => {
      const updatedItem: Item = action.payload;
      if (state.itemsById[updatedItem.uuid]) {
        state.itemsById[updatedItem.uuid] = updatedItem;
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
        const { uuid, data, hasMoreHistoricalItems, lastSeenInteractionCount } =
          sourceWithItems;
        state.sourceMetadata = {
          uuid,
          data,
          hasMoreHistoricalItems,
          lastSeenInteractionCount,
        };
        state.itemsById = Object.fromEntries(
          sourceWithItems.items.map((i) => [i.uuid, i]),
        );
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
        if (!action.payload || !state.sourceMetadata) {
          return;
        }
        const { items, hasMoreHistoricalItems } = action.payload;
        // Prepend older items by inserting them before existing entries.
        // Object insertion order is preserved, so Object.values() returns
        // older items first — matching the original array prepend behavior.
        const olderById = Object.fromEntries(
          items.filter((i) => !state.itemsById[i.uuid]).map((i) => [i.uuid, i]),
        );
        state.itemsById = { ...olderById, ...state.itemsById };
        state.hasMoreHistoricalItems = hasMoreHistoricalItems ?? false;
      })
      .addCase(fetchOlderConversationItems.rejected, (state) => {
        state.olderItemsLoading = false;
      })
      .addCase(updateItemFetchStatus.fulfilled, (state, action) => {
        const updatedItem = action.payload.item;
        if (updatedItem && state.itemsById[updatedItem.uuid]) {
          state.itemsById[updatedItem.uuid] = updatedItem;
        }
        state.lastFetchTime = Date.now();
      });
  },
});

export const { clearError, clearConversation, updateItem } =
  conversationSlice.actions;

// Internal selectors for createSelector inputs
const selectSourceMetadata = (state: RootState) =>
  state.conversation.sourceMetadata;
const selectItemsById = (state: RootState) => state.conversation.itemsById;

// Reconstructs SourceWithItems from normalized state; memoized so components
// only re-render when sourceMetadata or itemsById actually changes.
export const selectConversation = createSelector(
  selectSourceMetadata,
  selectItemsById,
  (_state: RootState, sourceUuid: string) => sourceUuid,
  (metadata, itemsById, sourceUuid): SourceWithItems | null => {
    if (!metadata || metadata.uuid !== sourceUuid) {
      return null;
    }
    return { ...metadata, items: Object.values(itemsById) };
  },
);

export const selectLastConversation = createSelector(
  selectSourceMetadata,
  selectItemsById,
  (metadata, itemsById): SourceWithItems | null => {
    if (!metadata) {
      return null;
    }
    return { ...metadata, items: Object.values(itemsById) };
  },
);

export const selectConversationLoading = (state: RootState) =>
  state.conversation.loading;
export const selectHasMoreHistoricalItems = (state: RootState) =>
  state.conversation.hasMoreHistoricalItems;
export const selectOlderItemsLoading = (state: RootState) =>
  state.conversation.olderItemsLoading;

export default conversationSlice.reducer;
