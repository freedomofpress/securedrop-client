import {
  createSlice,
  createAsyncThunk,
  createSelector,
  PayloadAction,
} from "@reduxjs/toolkit";

import type { RootState } from "../../store";
import {
  EventStatus,
  FetchStatus,
  type DownloadActivity,
  type Item,
  type PendingEventActivity,
  type SyncActivitySnapshot,
} from "../../../types";
import { setUnauth } from "../session/sessionSlice";
import { updateItem } from "../conversation/conversationSlice";
import { SyncActivity, selectSyncActivity } from "../sync/syncSlice";

export const RECENT_DOWNLOADS_LIMIT = 5;
export const COMPLETED_EVENTS_LIMIT = 50;
// How long a drained event lingers in the sidebar before it is dropped, so
// that work which syncs quickly is still legible
export const COMPLETED_EVENT_DISPLAY_MS = 5000;

const IN_FLIGHT_STATUSES: ReadonlySet<FetchStatus> = new Set([
  FetchStatus.DownloadInProgress,
  FetchStatus.DecryptionInProgress,
]);

const STALLED_STATUSES: ReadonlySet<FetchStatus> = new Set([
  FetchStatus.Paused,
  FetchStatus.FailedDownloadRetryable,
  FetchStatus.FailedDecryptionRetryable,
  FetchStatus.FailedTerminal,
]);

const FAILED_EVENT_STATUSES: ReadonlySet<EventStatus> = new Set([
  EventStatus.BadRequest,
  EventStatus.NotFound,
  // TODO: sometimes the Conflict code is resolvable, we may add
  // more nuanced handling
  EventStatus.Conflict,
  EventStatus.NotImplemented,
]);

export type CompletedEventActivity = PendingEventActivity & {
  // Renderer-side timestamp, used to age the event out of the sidebar
  completedAt: number;
};

export interface SyncActivityState {
  downloads: Record<string, DownloadActivity>;
  recentDownloads: DownloadActivity[];
  pendingEvents: PendingEventActivity[];
  inFlightEventIds: string[];
  // Events handed to the server at least once. An event that leaves the queue
  // without appearing here was superseded or purged locally, not synced.
  submittedEventIds: string[];
  completedEvents: CompletedEventActivity[];
  loading: boolean;
  error: string | null;
}

const initialState: SyncActivityState = {
  downloads: {},
  recentDownloads: [],
  pendingEvents: [],
  inFlightEventIds: [],
  submittedEventIds: [],
  completedEvents: [],
  loading: false,
  error: null,
};

export const fetchSyncActivity = createAsyncThunk(
  "syncActivity/fetchSyncActivity",
  async (): Promise<SyncActivitySnapshot> => {
    return window.electronAPI.getSyncActivity();
  },
);

const toDownloadActivity = (
  item: Item,
  previous?: DownloadActivity,
): DownloadActivity => ({
  itemUuid: item.uuid,
  sourceUuid: item.data.source,
  sourceDesignation: previous?.sourceDesignation ?? null,
  filename: item.filename,
  kind: item.data.kind,
  fetchStatus: item.fetch_status ?? FetchStatus.Initial,
  fetchProgress: item.fetch_progress,
  size: item.data.size,
  decryptedSize: item.decrypted_size,
  retryAttempts: previous?.retryAttempts ?? 0,
  updatedAt: Date.now(),
});

const recordCompletedEvents = (
  state: SyncActivityState,
  pendingEvents: PendingEventActivity[],
) => {
  const stillPending = new Set(pendingEvents.map((event) => event.id));
  const submitted = new Set(state.submittedEventIds);
  const completedAt = Date.now();

  // Only events that reached the server count as done. Coalesced star toggles
  // and events purged by a source deletion also leave the queue, but showing
  // those as synced would be a lie.
  const completed = state.pendingEvents
    .filter((event) => !stillPending.has(event.id) && submitted.has(event.id))
    .map((event) => ({ ...event, completedAt }));

  state.submittedEventIds = state.submittedEventIds.filter((id) =>
    stillPending.has(id),
  );

  if (completed.length === 0) {
    return;
  }

  state.completedEvents.unshift(...completed.reverse());
  state.completedEvents.length = Math.min(
    state.completedEvents.length,
    COMPLETED_EVENTS_LIMIT,
  );
};

export const syncActivitySlice = createSlice({
  name: "syncActivity",
  initialState,
  reducers: {
    setEventsInFlight: (state, action: PayloadAction<string[]>) => {
      state.inFlightEventIds = action.payload;
      // The queue is cleared before the events are deleted, so remember what
      // went out rather than reading inFlightEventIds when they disappear
      const submitted = new Set(state.submittedEventIds);
      for (const id of action.payload) {
        submitted.add(id);
      }
      state.submittedEventIds = [...submitted];
    },
    pruneCompletedEvents: (state, action: PayloadAction<number>) => {
      const remaining = state.completedEvents.filter(
        (event) => event.completedAt > action.payload,
      );
      // Reassigning unconditionally would re-arm the eviction timer on every
      // prune, even the ones that drop nothing
      if (remaining.length !== state.completedEvents.length) {
        state.completedEvents = remaining;
      }
    },
    clearRecentDownloads: (state) => {
      state.recentDownloads = [];
    },
    clearCompletedEvents: (state) => {
      state.completedEvents = [];
    },
  },
  extraReducers: (builder) => {
    builder
      .addCase(setUnauth.fulfilled, () => initialState)
      .addCase(updateItem, (state, action) => {
        const item: Item = action.payload;
        const status = item.fetch_status ?? FetchStatus.Initial;
        const previous = state.downloads[item.uuid];

        if (status === FetchStatus.Complete) {
          if (previous) {
            delete state.downloads[item.uuid];
            state.recentDownloads.unshift(toDownloadActivity(item, previous));
            state.recentDownloads.length = Math.min(
              state.recentDownloads.length,
              RECENT_DOWNLOADS_LIMIT,
            );
          }
          return;
        }

        if (IN_FLIGHT_STATUSES.has(status) || STALLED_STATUSES.has(status)) {
          state.downloads[item.uuid] = toDownloadActivity(item, previous);
          return;
        }

        // Otherwise it is cancelled or scheduled for deletion
        delete state.downloads[item.uuid];
      })
      .addCase(fetchSyncActivity.pending, (state) => {
        state.loading = true;
      })
      .addCase(fetchSyncActivity.fulfilled, (state, action) => {
        state.loading = false;
        state.error = null;
        recordCompletedEvents(state, action.payload.pendingEvents);
        state.pendingEvents = action.payload.pendingEvents;
        state.downloads = Object.fromEntries(
          action.payload.downloads.map((download) => {
            const streamed = state.downloads[download.itemUuid];
            return [
              download.itemUuid,
              streamed
                ? { ...download, fetchProgress: streamed.fetchProgress }
                : download,
            ];
          }),
        );
      })
      .addCase(fetchSyncActivity.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to read sync activity";
      });
  },
});

export const {
  setEventsInFlight,
  pruneCompletedEvents,
  clearRecentDownloads,
  clearCompletedEvents,
} = syncActivitySlice.actions;

export enum PendingEventDisplayStatus {
  QUEUED = "queued",
  SENDING = "sending",
  NEEDS_ATTENTION = "needsAttention",
}

export type PendingEventWithStatus = PendingEventActivity & {
  displayStatus: PendingEventDisplayStatus;
};

export enum DownloadDisplayStatus {
  QUEUED = "queued",
  DOWNLOADING = "downloading",
  DECRYPTING = "decrypting",
  STOPPED = "stopped",
  NEEDS_ATTENTION = "needsAttention",
}

export type DownloadWithStatus = DownloadActivity & {
  displayStatus: DownloadDisplayStatus;
};

const pendingEventDisplayStatus = (
  event: PendingEventActivity,
  inFlightEventIds: string[],
): PendingEventDisplayStatus => {
  if (inFlightEventIds.includes(event.id)) {
    return PendingEventDisplayStatus.SENDING;
  }
  if (
    event.lastEventStatus !== null &&
    FAILED_EVENT_STATUSES.has(event.lastEventStatus)
  ) {
    return PendingEventDisplayStatus.NEEDS_ATTENTION;
  }
  return PendingEventDisplayStatus.QUEUED;
};

const downloadDisplayStatus = (
  download: DownloadActivity,
): DownloadDisplayStatus => {
  switch (download.fetchStatus) {
    case FetchStatus.DownloadInProgress:
      return DownloadDisplayStatus.DOWNLOADING;
    case FetchStatus.DecryptionInProgress:
      return DownloadDisplayStatus.DECRYPTING;
    case FetchStatus.Paused:
      return DownloadDisplayStatus.STOPPED;
    case FetchStatus.FailedDownloadRetryable:
    case FetchStatus.FailedDecryptionRetryable:
    case FetchStatus.FailedTerminal:
      return DownloadDisplayStatus.NEEDS_ATTENTION;
    default:
      return DownloadDisplayStatus.QUEUED;
  }
};

export const selectSyncActivityLoading = (state: RootState) =>
  state.syncActivity.loading;
export const selectSyncActivityError = (state: RootState) =>
  state.syncActivity.error;
export const selectRecentDownloads = (state: RootState) =>
  state.syncActivity.recentDownloads;
// Events that finished syncing recently, still shown while they age out.
export const selectCompletedEvents = (
  state: RootState,
): CompletedEventActivity[] => state.syncActivity.completedEvents;

// Memoized so subscribing components only re-render when the queue itself moves
export const selectPendingEventActivity = createSelector(
  [
    (state: RootState) => state.syncActivity.pendingEvents,
    (state: RootState) => state.syncActivity.inFlightEventIds,
  ],
  (pendingEvents, inFlightEventIds): PendingEventWithStatus[] =>
    pendingEvents.map((event) => ({
      ...event,
      displayStatus: pendingEventDisplayStatus(event, inFlightEventIds),
    })),
);

export const selectDownloadActivity = createSelector(
  [(state: RootState) => state.syncActivity.downloads],
  (downloads): DownloadWithStatus[] =>
    Object.values(downloads).map((download) => ({
      ...download,
      displayStatus: downloadDisplayStatus(download),
    })),
);

export const selectNeedsAttentionCount = (state: RootState): number => {
  const events = state.syncActivity.pendingEvents.filter(
    (event) =>
      event.lastEventStatus !== null &&
      FAILED_EVENT_STATUSES.has(event.lastEventStatus),
  ).length;
  const downloads = Object.values(state.syncActivity.downloads).filter(
    (download) =>
      download.fetchStatus === FetchStatus.FailedDownloadRetryable ||
      download.fetchStatus === FetchStatus.FailedDecryptionRetryable ||
      download.fetchStatus === FetchStatus.FailedTerminal,
  ).length;
  return events + downloads;
};

export const selectHasActivityInFlight = (state: RootState): boolean =>
  state.syncActivity.inFlightEventIds.length > 0 ||
  Object.values(state.syncActivity.downloads).some((download) =>
    IN_FLIGHT_STATUSES.has(download.fetchStatus),
  );

export const selectPendingEventCount = (state: RootState): number =>
  state.syncActivity.pendingEvents.length;

export const selectSyncSummary = (state: RootState): SyncActivity => {
  const transport = selectSyncActivity(state);

  if (transport === SyncActivity.SYNCING || selectHasActivityInFlight(state)) {
    return SyncActivity.SYNCING;
  }
  if (
    transport === SyncActivity.NEEDS_ATTENTION ||
    selectNeedsAttentionCount(state) > 0
  ) {
    return SyncActivity.NEEDS_ATTENTION;
  }
  return SyncActivity.UP_TO_DATE;
};

export default syncActivitySlice.reducer;
