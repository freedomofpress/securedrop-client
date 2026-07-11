import {
  createSlice,
  createAsyncThunk,
  createAction,
  type ActionReducerMapBuilder,
} from "@reduxjs/toolkit";
import {
  Item,
  NONPROCESSABLE_FETCH_STATUSES,
  PendingEventType,
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
  traversalEpoch: number;
  traversalSourceUuid: string | null;
  activeConversationRequest: ConversationRequest | null;
  activeOlderRequest: OlderConversationRequest | null;
}

interface ConversationRequest {
  sourceUuid: string;
  traversalEpoch: number;
  requestId: string;
}

interface OlderConversationRequest extends ConversationRequest {
  requestedGeneration: number | undefined;
}

const initialState: ConversationState = {
  conversation: null,
  loading: false,
  error: null,
  lastFetchTime: null,
  hasMoreHistoricalItems: false,
  olderItemsLoading: false,
  traversalEpoch: 0,
  traversalSourceUuid: null,
  activeConversationRequest: null,
  activeOlderRequest: null,
};

const CONVERSATION_PAGE_SIZE = 100;

interface OlderConversationItemsResult {
  request: OlderConversationRequest;
  sourceWithItems: SourceWithItems;
}

interface ConversationItemsResult {
  request: ConversationRequest;
  sourceWithItems: SourceWithItems;
}

interface ConversationFetchError {
  message: string;
  request: ConversationRequest;
}

interface OlderConversationFetchError {
  message: string;
  request: OlderConversationRequest;
}

interface PendingSeenEffect {
  created: boolean;
  token: string;
}

interface OlderConversationTraversal {
  beforeInteractionCount: number | null | undefined;
  beforeItemUuid: string | undefined;
  request: OlderConversationRequest;
}

type OlderConversationCursor = Omit<OlderConversationTraversal, "request">;

const commitConversationPage = createAction<ConversationItemsResult>(
  "conversation/commitConversationPage",
);
const commitOlderConversationPage = createAction<OlderConversationItemsResult>(
  "conversation/commitOlderConversationPage",
);

function sameConversationRequest(
  first: ConversationRequest | null,
  second: ConversationRequest,
): boolean {
  return (
    first?.sourceUuid === second.sourceUuid &&
    first.traversalEpoch === second.traversalEpoch &&
    first.requestId === second.requestId
  );
}

function isActiveConversationRequest(
  state: ConversationState,
  request: ConversationRequest,
): boolean {
  return (
    sameConversationRequest(state.activeConversationRequest, request) &&
    request.traversalEpoch === state.traversalEpoch &&
    state.traversalSourceUuid === request.sourceUuid
  );
}

function sameOlderRequest(
  first: OlderConversationRequest | null,
  second: OlderConversationRequest,
): boolean {
  return (
    sameConversationRequest(first, second) &&
    first?.requestedGeneration === second.requestedGeneration
  );
}

function isActiveOlderRequest(
  state: ConversationState,
  request: OlderConversationRequest,
  actionRequestId: string,
): boolean {
  return (
    actionRequestId === request.requestId &&
    sameOlderRequest(state.activeOlderRequest, request) &&
    state.traversalEpoch === request.traversalEpoch &&
    state.traversalSourceUuid === request.sourceUuid
  );
}

function hasAcceptableGeneration(
  conversation: SourceWithItems,
  page: SourceWithItems,
  request: OlderConversationRequest,
): boolean {
  if (conversation.paginationGeneration !== request.requestedGeneration) {
    return false;
  }
  if (page.paginationRestarted) {
    return page.paginationGeneration !== request.requestedGeneration;
  }
  return page.paginationGeneration === request.requestedGeneration;
}

function canAcceptOlderPage(
  state: ConversationState,
  page: SourceWithItems,
  request: OlderConversationRequest,
): boolean {
  const conversation = state.conversation;
  if (!conversation || conversation.uuid !== request.sourceUuid) {
    return false;
  }
  if (page.uuid !== request.sourceUuid) {
    return false;
  }
  return hasAcceptableGeneration(conversation, page, request);
}

function activeConversationRequest(
  state: ConversationState,
  sourceUuid: string,
  requestId: string,
): ConversationRequest {
  const request = state.activeConversationRequest;
  if (
    !request ||
    request.sourceUuid !== sourceUuid ||
    request.requestId !== requestId
  ) {
    throw new Error("Conversation request is no longer active");
  }
  return { ...request };
}

function requestToken(request: ConversationRequest): string {
  return [request.sourceUuid, request.traversalEpoch, request.requestId].join(
    ":",
  );
}

function pageGenerationIsCurrent(page: SourceWithItems): boolean {
  return (
    window.electronAPI.getConversationPaginationGeneration() ===
    page.paginationGeneration
  );
}

function rejectionMessage(error: unknown, fallback: string): string {
  if (error instanceof Error) {
    return error.message || fallback;
  }
  return typeof error === "string" ? error : fallback;
}

async function requestConversationPage(
  sourceUuid: string,
  options: Parameters<typeof window.electronAPI.getSourceWithItems>[1],
): Promise<SourceWithItems> {
  const page = await window.electronAPI.getSourceWithItems(sourceUuid, options);
  if (page.uuid !== sourceUuid) {
    throw new Error("Conversation response source does not match request");
  }
  return page;
}

async function beginConversationSeen(
  page: SourceWithItems,
  request: ConversationRequest,
): Promise<PendingSeenEffect | null> {
  const maxInteractionCount = page.items.reduce(
    (max, item) => Math.max(max, item.data.interaction_count ?? 0),
    0,
  );
  if (maxInteractionCount <= 0) {
    return null;
  }
  const token = requestToken(request);
  const created = await window.electronAPI.addPendingSourceConversationSeen(
    request.sourceUuid,
    maxInteractionCount,
    token,
  );
  return { created: created !== null, token };
}

async function rollbackConversationSeen(
  request: ConversationRequest,
  effect: PendingSeenEffect | null,
): Promise<void> {
  if (!effect) {
    return;
  }
  await window.electronAPI.finalizePendingSourceConversationSeen(
    request.sourceUuid,
    effect.token,
    false,
  );
}

function confirmConversationSeen(
  request: ConversationRequest,
  effect: PendingSeenEffect | null,
  dispatch: (action: ReturnType<typeof fetchSources>) => unknown,
): void {
  if (!effect) {
    return;
  }
  if (effect.created) {
    dispatch(fetchSources());
  }
  void window.electronAPI.finalizePendingSourceConversationSeen(
    request.sourceUuid,
    effect.token,
    true,
  );
}

function conversationWasCommitted(
  state: ConversationState,
  request: ConversationRequest,
  page: SourceWithItems,
): boolean {
  return (
    state.activeConversationRequest === null &&
    state.traversalEpoch === request.traversalEpoch &&
    state.traversalSourceUuid === request.sourceUuid &&
    state.conversation?.uuid === page.uuid &&
    state.conversation.paginationGeneration === page.paginationGeneration
  );
}

function olderPageWasCommitted(
  state: ConversationState,
  request: OlderConversationRequest,
): boolean {
  return (
    state.activeOlderRequest === null &&
    state.traversalEpoch === request.traversalEpoch &&
    state.traversalSourceUuid === request.sourceUuid
  );
}

function oldestConversationCursor(
  conversation: SourceWithItems,
): OlderConversationCursor {
  const paginationCursor = conversation.paginationCursor;
  if (paginationCursor) {
    return {
      beforeInteractionCount: paginationCursor.interactionCount,
      beforeItemUuid: paginationCursor.itemUuid,
    };
  }
  const oldestItem = conversation.items[0];
  return {
    beforeInteractionCount: oldestItem?.data.interaction_count,
    beforeItemUuid: oldestItem?.uuid,
  };
}

function captureOlderConversationTraversal(
  state: ConversationState,
  sourceUuid: string,
  requestId: string,
): OlderConversationTraversal {
  const conversation = state.conversation;
  const request = state.activeOlderRequest;
  if (
    !conversation ||
    !request ||
    request.requestId !== requestId ||
    request.sourceUuid !== sourceUuid
  ) {
    throw new Error("Older conversation request is no longer active");
  }
  return {
    ...oldestConversationCursor(conversation),
    request: { ...request },
  };
}

function commitValidatedOlderPage(
  state: ConversationState,
  sourceWithItems: SourceWithItems,
  request: OlderConversationRequest,
  dispatch: (action: ReturnType<typeof commitOlderConversationPage>) => unknown,
): void {
  if (!canAcceptOlderPage(state, sourceWithItems, request)) {
    throw new Error("Older conversation response cannot be committed");
  }
  dispatch(commitOlderConversationPage({ request, sourceWithItems }));
}

export const fetchConversation = createAsyncThunk<
  ConversationItemsResult,
  string,
  { rejectValue: ConversationFetchError }
>(
  "conversation/fetchConversation",
  async (sourceUuid, { dispatch, getState, rejectWithValue, requestId }) => {
    const request = activeConversationRequest(
      (getState() as RootState).conversation,
      sourceUuid,
      requestId,
    );
    const requestIsActive = () =>
      isActiveConversationRequest(
        (getState() as RootState).conversation,
        request,
      );
    try {
      while (requestIsActive()) {
        const sourceWithItems = await requestConversationPage(sourceUuid, {
          limit: CONVERSATION_PAGE_SIZE,
        });
        if (!requestIsActive() || !pageGenerationIsCurrent(sourceWithItems)) {
          continue;
        }
        const seenEffect = await beginConversationSeen(
          sourceWithItems,
          request,
        );
        if (!requestIsActive() || !pageGenerationIsCurrent(sourceWithItems)) {
          await rollbackConversationSeen(request, seenEffect);
          continue;
        }
        dispatch(commitConversationPage({ request, sourceWithItems }));
        const state = (getState() as RootState).conversation;
        if (conversationWasCommitted(state, request, sourceWithItems)) {
          confirmConversationSeen(request, seenEffect, dispatch);
          return { request, sourceWithItems };
        }
        await rollbackConversationSeen(request, seenEffect);
      }
      throw new Error("Conversation request was superseded");
    } catch (error) {
      const message = rejectionMessage(error, "Failed to fetch conversation");
      return rejectWithValue({ message, request });
    }
  },
);

export const fetchOlderConversationItems = createAsyncThunk<
  OlderConversationItemsResult,
  string,
  { rejectValue: OlderConversationFetchError }
>(
  "conversation/fetchOlderConversationItems",
  async (sourceUuid, { dispatch, getState, rejectWithValue, requestId }) => {
    const traversal = captureOlderConversationTraversal(
      (getState() as RootState).conversation,
      sourceUuid,
      requestId,
    );
    const capturedRequest = traversal.request;
    const requestIsActive = () =>
      isActiveOlderRequest(
        (getState() as RootState).conversation,
        capturedRequest,
        requestId,
      );

    try {
      while (requestIsActive()) {
        const sourceWithItems = await requestConversationPage(sourceUuid, {
          limit: CONVERSATION_PAGE_SIZE,
          beforeInteractionCount: traversal.beforeInteractionCount,
          beforeItemUuid: traversal.beforeItemUuid,
          paginationGeneration: capturedRequest.requestedGeneration,
        });
        if (!requestIsActive() || !pageGenerationIsCurrent(sourceWithItems)) {
          continue;
        }
        commitValidatedOlderPage(
          (getState() as RootState).conversation,
          sourceWithItems,
          capturedRequest,
          dispatch,
        );
        const state = (getState() as RootState).conversation;
        if (olderPageWasCommitted(state, capturedRequest)) {
          return { request: capturedRequest, sourceWithItems };
        }
      }
      throw new Error("Older conversation request was superseded");
    } catch (error) {
      const message = rejectionMessage(
        error,
        "Failed to fetch older conversation items",
      );
      return rejectWithValue({ message, request: capturedRequest });
    }
  },
  {
    condition: (sourceUuid, { getState }) => {
      const state = (getState() as RootState).conversation;
      return (
        state.conversation?.uuid === sourceUuid &&
        state.traversalSourceUuid === sourceUuid &&
        state.activeConversationRequest === null &&
        state.hasMoreHistoricalItems &&
        !state.olderItemsLoading
      );
    },
  },
);

export const updateItemFetchStatus = createAsyncThunk(
  "conversation/updateItemFetchStatus",
  async ({
    itemUuid,
    fetchStatus,
  }: {
    sourceUuid: string;
    itemUuid: string;
    fetchStatus: number;
  }) => {
    await window.electronAPI.updateFetchStatus(itemUuid, fetchStatus);
    const item = await window.electronAPI.getItem(itemUuid);
    return { item };
  },
);

export const deleteItem = createAsyncThunk(
  "conversation/deleteItem",
  async ({
    sourceUuid,
    itemUuid,
  }: {
    sourceUuid: string;
    itemUuid: string;
  }) => {
    await window.electronAPI.addPendingItemEvent(
      itemUuid,
      PendingEventType.ItemDeleted,
    );
    const sourceWithItems =
      await window.electronAPI.getSourceWithItems(sourceUuid);
    return { sourceWithItems };
  },
);

function addConversationFetchReducers(
  builder: ActionReducerMapBuilder<ConversationState>,
): void {
  builder
    .addCase(fetchConversation.pending, (state, action) => {
      state.traversalEpoch += 1;
      state.traversalSourceUuid = action.meta.arg;
      state.activeConversationRequest = {
        sourceUuid: action.meta.arg,
        traversalEpoch: state.traversalEpoch,
        requestId: action.meta.requestId,
      };
      state.activeOlderRequest = null;
      state.loading = true;
      state.olderItemsLoading = false;
      state.error = null;
    })
    .addCase(commitConversationPage, (state, action) => {
      const { request, sourceWithItems } = action.payload;
      if (!isActiveConversationRequest(state, request)) {
        return;
      }
      state.activeConversationRequest = null;
      state.loading = false;
      state.error = null;
      state.conversation = sourceWithItems;
      state.hasMoreHistoricalItems =
        sourceWithItems.hasMoreHistoricalItems ?? false;
      state.lastFetchTime = Date.now();
    })
    .addCase(fetchConversation.rejected, (state, action) => {
      const failure = action.payload;
      if (!failure || !isActiveConversationRequest(state, failure.request)) {
        return;
      }
      state.activeConversationRequest = null;
      state.loading = false;
      state.error = failure.message;
    });
}

function addOlderConversationFetchReducers(
  builder: ActionReducerMapBuilder<ConversationState>,
): void {
  builder
    .addCase(fetchOlderConversationItems.pending, (state, action) => {
      const conversation = state.conversation;
      if (!conversation) {
        return;
      }
      state.activeOlderRequest = {
        sourceUuid: action.meta.arg,
        traversalEpoch: state.traversalEpoch,
        requestId: action.meta.requestId,
        requestedGeneration: conversation.paginationGeneration,
      };
      state.olderItemsLoading = true;
    })
    .addCase(commitOlderConversationPage, (state, action) => {
      const { request, sourceWithItems } = action.payload;
      if (!isActiveOlderRequest(state, request, request.requestId)) {
        return;
      }
      const conversation = state.conversation;
      if (
        !conversation ||
        !canAcceptOlderPage(state, sourceWithItems, request)
      ) {
        return;
      }
      state.activeOlderRequest = null;
      state.olderItemsLoading = false;
      const { items, hasMoreHistoricalItems } = sourceWithItems;
      if (sourceWithItems.paginationRestarted) {
        state.conversation = sourceWithItems;
        state.hasMoreHistoricalItems = hasMoreHistoricalItems ?? false;
        return;
      }
      const existingUuids = new Set(
        conversation.items.map((item) => item.uuid),
      );
      const olderItems = items.filter((item) => !existingUuids.has(item.uuid));
      conversation.items = [...olderItems, ...conversation.items];
      if (sourceWithItems.paginationCursor) {
        conversation.paginationCursor = sourceWithItems.paginationCursor;
      }
      conversation.paginationGeneration = sourceWithItems.paginationGeneration;
      conversation.hasMoreHistoricalItems = hasMoreHistoricalItems;
      state.hasMoreHistoricalItems = hasMoreHistoricalItems ?? false;
    })
    .addCase(fetchOlderConversationItems.rejected, (state, action) => {
      const failure = action.payload;
      if (
        !failure ||
        !isActiveOlderRequest(state, failure.request, action.meta.requestId)
      ) {
        return;
      }
      state.activeOlderRequest = null;
      state.olderItemsLoading = false;
    });
}

function addConversationMutationReducers(
  builder: ActionReducerMapBuilder<ConversationState>,
): void {
  builder
    .addCase(updateItemFetchStatus.fulfilled, (state, action) => {
      const { item: updatedItem } = action.payload;
      if (state.conversation) {
        state.conversation.items = state.conversation.items.map((item) => {
          if (updatedItem && item.uuid === updatedItem.uuid) {
            return updatedItem;
          }
          return item;
        });
      }
      state.lastFetchTime = Date.now();
    })
    .addCase(deleteItem.fulfilled, (state, action) => {
      const { sourceWithItems } = action.payload;
      state.conversation = sourceWithItems;
      state.lastFetchTime = Date.now();
    });
}

const conversationSlice = createSlice({
  name: "conversation",
  initialState,
  reducers: {
    clearError: (state) => {
      state.error = null;
    },
    clearConversation: (state) => {
      state.conversation = null;
      state.loading = false;
      state.lastFetchTime = null;
      state.hasMoreHistoricalItems = false;
      state.olderItemsLoading = false;
      state.traversalEpoch += 1;
      state.traversalSourceUuid = null;
      state.activeConversationRequest = null;
      state.activeOlderRequest = null;
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
    addConversationFetchReducers(builder);
    addOlderConversationFetchReducers(builder);
    addConversationMutationReducers(builder);
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
