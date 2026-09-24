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
  type ActivitySnapshot,
} from "../../../types";
import { setUnauth } from "../session/sessionSlice";
import { updateItem } from "../conversation/conversationSlice";
import { SyncActivity, selectSyncActivity } from "../sync/syncSlice";

export const RECENT_DOWNLOADS_LIMIT = 5;
export const COMPLETED_EVENTS_LIMIT = 50;

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
  // Renderer-side timestamp to order events
  completedAt: number;
};

export interface ActivityState {
  downloads: Record<string, DownloadActivity>;
  recentDownloads: DownloadActivity[];
  pendingEvents: PendingEventActivity[];
  inFlightEventIds: string[];
  completedEvents: CompletedEventActivity[];
  loading: boolean;
  error: string | null;
}

const initialState: ActivityState = {
  downloads: {},
  recentDownloads: [],
  pendingEvents: [],
  inFlightEventIds: [],
  completedEvents: [],
  loading: false,
  error: null,
};

export const fetchActivity = createAsyncThunk(
  "activity/fetchActivity",
  async (): Promise<ActivitySnapshot> => {
    return window.electronAPI.getActivity();
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
  state: ActivityState,
  pendingEvents: PendingEventActivity[],
) => {
  const stillPending = new Set(pendingEvents.map((event) => event.id));
  const completedAt = Date.now();

  const completed = state.pendingEvents
    .filter((event) => !stillPending.has(event.id))
    .map((event) => ({ ...event, completedAt }));

  if (completed.length === 0) {
    return;
  }

  state.completedEvents.unshift(...completed.reverse());
  state.completedEvents.length = Math.min(
    state.completedEvents.length,
    COMPLETED_EVENTS_LIMIT,
  );
};

export const activitySlice = createSlice({
  name: "activity",
  initialState,
  reducers: {
    setEventsInFlight: (state, action: PayloadAction<string[]>) => {
      state.inFlightEventIds = action.payload;
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
      .addCase(fetchActivity.pending, (state) => {
        state.loading = true;
      })
      .addCase(fetchActivity.fulfilled, (state, action) => {
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
      .addCase(fetchActivity.rejected, (state, action) => {
        state.loading = false;
        state.error = action.error.message || "Failed to read activity";
      });
  },
});

export const { setEventsInFlight, clearRecentDownloads, clearCompletedEvents } =
  activitySlice.actions;

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

export const selectActivityLoading = (state: RootState) =>
  state.activity.loading;
export const selectActivityError = (state: RootState) => state.activity.error;
export const selectRecentDownloads = (state: RootState) =>
  state.activity.recentDownloads;
// Session-local activity log: events that left the queue since sign in.
export const selectCompletedEvents = (
  state: RootState,
): CompletedEventActivity[] => state.activity.completedEvents;

export const selectPendingEventActivity = (
  state: RootState,
): PendingEventWithStatus[] =>
  state.activity.pendingEvents.map((event) => ({
    ...event,
    displayStatus: pendingEventDisplayStatus(
      event,
      state.activity.inFlightEventIds,
    ),
  }));

export const selectDownloadActivity = createSelector(
  [(state: RootState) => state.activity.downloads],
  (downloads): DownloadWithStatus[] =>
    Object.values(downloads).map((download) => ({
      ...download,
      displayStatus: downloadDisplayStatus(download),
    })),
);

export const selectNeedsAttentionCount = (state: RootState): number => {
  const events = state.activity.pendingEvents.filter(
    (event) =>
      event.lastEventStatus !== null &&
      FAILED_EVENT_STATUSES.has(event.lastEventStatus),
  ).length;
  const downloads = Object.values(state.activity.downloads).filter(
    (download) =>
      download.fetchStatus === FetchStatus.FailedDownloadRetryable ||
      download.fetchStatus === FetchStatus.FailedDecryptionRetryable ||
      download.fetchStatus === FetchStatus.FailedTerminal,
  ).length;
  return events + downloads;
};

export const selectHasActivityInFlight = (state: RootState): boolean =>
  state.activity.inFlightEventIds.length > 0 ||
  Object.values(state.activity.downloads).some((download) =>
    IN_FLIGHT_STATUSES.has(download.fetchStatus),
  );

export const selectPendingEventCount = (state: RootState): number =>
  state.activity.pendingEvents.length;

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

export default activitySlice.reducer;
