import { describe, it, expect, beforeEach, vi } from "vitest";

import { setupStore } from "../../store";
import type { RootState } from "../../store";
import {
  EventStatus,
  FetchStatus,
  PendingEventType,
  type DownloadActivity,
  type Item,
  type PendingEventActivity,
} from "../../../types";
import { updateItem } from "../conversation/conversationSlice";
import { setUnauth } from "../session/sessionSlice";
import { SyncActivity } from "../sync/syncSlice";
import reducer, {
  COMPLETED_EVENTS_LIMIT,
  DownloadDisplayStatus,
  PendingEventDisplayStatus,
  RECENT_DOWNLOADS_LIMIT,
  clearCompletedEvents,
  clearRecentDownloads,
  fetchSyncActivity,
  selectCompletedEvents,
  selectDownloadActivity,
  selectHasActivityInFlight,
  selectNeedsAttentionCount,
  selectPendingEventActivity,
  selectRecentDownloads,
  selectSyncSummary,
  setEventsInFlight,
  type SyncActivityState,
} from "./syncActivitySlice";

const mockElectronAPI = {
  getSyncActivity: vi.fn(),
};

Object.defineProperty(window, "electronAPI", {
  value: mockElectronAPI,
  writable: true,
});

const initialState: SyncActivityState = {
  downloads: {},
  recentDownloads: [],
  pendingEvents: [],
  inFlightEventIds: [],
  completedEvents: [],
  loading: false,
  error: null,
};

const makeItem = (
  uuid: string,
  fetchStatus: FetchStatus,
  overrides: Partial<Item> = {},
): Item =>
  ({
    uuid,
    data: {
      kind: "file",
      source: "source-1",
      uuid,
    },
    plaintext: null,
    filename: `${uuid}.pdf`,
    fetch_status: fetchStatus,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
    ...overrides,
  }) as Item;

const makeDownload = (
  itemUuid: string,
  fetchStatus: FetchStatus,
): DownloadActivity => ({
  itemUuid,
  sourceUuid: "source-1",
  sourceDesignation: "Crimson Falcon",
  filename: `${itemUuid}.pdf`,
  kind: "file",
  fetchStatus,
  fetchProgress: null,
  decryptedSize: null,
  retryAttempts: 0,
  updatedAt: 1000,
});

const makeEvent = (
  id: string,
  overrides: Partial<PendingEventActivity> = {},
): PendingEventActivity => ({
  id,
  type: PendingEventType.SourceDeleted,
  sourceUuid: "source-1",
  itemUuid: null,
  sourceDesignation: "Aged Sutler",
  filename: null,
  retryAttempts: 0,
  lastEventStatus: null,
  ...overrides,
});

const snapshotOf = (pendingEvents: PendingEventActivity[]) =>
  fetchSyncActivity.fulfilled({ downloads: [], pendingEvents }, "", undefined);

const stateWith = (
  syncActivity: Partial<SyncActivityState>,
  sync: Partial<RootState["sync"]> = {},
): RootState =>
  ({
    syncActivity: { ...initialState, ...syncActivity },
    sync: {
      error: null,
      lastSyncStarted: null,
      lastSyncFinished: null,
      status: null,
      ...sync,
    },
  }) as RootState;

describe("syncActivitySlice", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe("item update stream", () => {
    it("tracks a download that starts", () => {
      const state = reducer(
        initialState,
        updateItem(makeItem("item-1", FetchStatus.DownloadInProgress)),
      );

      expect(state.downloads["item-1"]).toMatchObject({
        itemUuid: "item-1",
        sourceUuid: "source-1",
        filename: "item-1.pdf",
        fetchStatus: FetchStatus.DownloadInProgress,
      });
    });

    it("keeps a stalled download so the user can act on it", () => {
      let state = reducer(
        initialState,
        updateItem(makeItem("item-1", FetchStatus.DownloadInProgress)),
      );
      state = reducer(
        state,
        updateItem(makeItem("item-1", FetchStatus.Paused)),
      );

      expect(state.downloads["item-1"].fetchStatus).toBe(FetchStatus.Paused);
      expect(state.recentDownloads).toHaveLength(0);
    });

    it("moves a completed download into recents", () => {
      let state = reducer(
        initialState,
        updateItem(makeItem("item-1", FetchStatus.DownloadInProgress)),
      );
      state = reducer(
        state,
        updateItem(makeItem("item-1", FetchStatus.Complete)),
      );

      expect(state.downloads).toEqual({});
      expect(state.recentDownloads).toHaveLength(1);
      expect(state.recentDownloads[0].itemUuid).toBe("item-1");
    });

    it("ignores a completion for a download it was not watching", () => {
      // Opening an old conversation replays completed items through the same
      // stream; those must not masquerade as recent activity.
      const state = reducer(
        initialState,
        updateItem(makeItem("item-old", FetchStatus.Complete)),
      );

      expect(state.recentDownloads).toHaveLength(0);
      expect(state.downloads).toEqual({});
    });

    it("caps recents and keeps the newest first", () => {
      let state = initialState;
      for (let i = 0; i < RECENT_DOWNLOADS_LIMIT + 3; i++) {
        state = reducer(
          state,
          updateItem(makeItem(`item-${i}`, FetchStatus.DownloadInProgress)),
        );
        state = reducer(
          state,
          updateItem(makeItem(`item-${i}`, FetchStatus.Complete)),
        );
      }

      expect(state.recentDownloads).toHaveLength(RECENT_DOWNLOADS_LIMIT);
      expect(state.recentDownloads[0].itemUuid).toBe(
        `item-${RECENT_DOWNLOADS_LIMIT + 2}`,
      );
    });

    it("drops a cancelled download entirely", () => {
      let state = reducer(
        initialState,
        updateItem(makeItem("item-1", FetchStatus.DownloadInProgress)),
      );
      state = reducer(
        state,
        updateItem(makeItem("item-1", FetchStatus.Cancelled)),
      );

      expect(state.downloads).toEqual({});
      expect(state.recentDownloads).toHaveLength(0);
    });

    it("carries the designation from the snapshot across a stream update", () => {
      // The item stream has no source designation, so it must survive from
      // whatever the last snapshot knew.
      let state = reducer(
        initialState,
        fetchSyncActivity.fulfilled(
          {
            downloads: [makeDownload("item-1", FetchStatus.DownloadInProgress)],
            pendingEvents: [],
          },
          "",
          undefined,
        ),
      );
      state = reducer(
        state,
        updateItem(
          makeItem("item-1", FetchStatus.DownloadInProgress, {
            fetch_progress: 4096,
          }),
        ),
      );

      expect(state.downloads["item-1"]).toMatchObject({
        sourceDesignation: "Crimson Falcon",
        fetchProgress: 4096,
      });
    });
  });

  describe("snapshot", () => {
    it("replaces the outstanding set but keeps streamed progress", () => {
      let state = reducer(
        initialState,
        updateItem(
          makeItem("item-1", FetchStatus.DownloadInProgress, {
            fetch_progress: 8192,
          }),
        ),
      );
      state = reducer(
        state,
        updateItem(makeItem("item-stale", FetchStatus.DownloadInProgress)),
      );

      state = reducer(
        state,
        fetchSyncActivity.fulfilled(
          {
            downloads: [makeDownload("item-1", FetchStatus.DownloadInProgress)],
            pendingEvents: [makeEvent("event-1")],
          },
          "",
          undefined,
        ),
      );

      // The snapshot is authoritative about what is outstanding.
      expect(Object.keys(state.downloads)).toEqual(["item-1"]);
      // But it cannot see progress ticks that arrived after it was taken.
      expect(state.downloads["item-1"].fetchProgress).toBe(8192);
      expect(state.pendingEvents).toHaveLength(1);
      expect(state.loading).toBe(false);
    });

    it("records a read failure", () => {
      const state = reducer(
        initialState,
        fetchSyncActivity.rejected(new Error("database is locked"), ""),
      );

      expect(state.loading).toBe(false);
      expect(state.error).toBe("database is locked");
    });

    it("reads the snapshot over IPC", async () => {
      const store = setupStore();
      const snapshot = {
        downloads: [makeDownload("item-1", FetchStatus.DownloadInProgress)],
        pendingEvents: [makeEvent("event-1")],
      };
      mockElectronAPI.getSyncActivity.mockResolvedValue(snapshot);

      await store.dispatch(fetchSyncActivity());

      expect(mockElectronAPI.getSyncActivity).toHaveBeenCalledTimes(1);
      expect(store.getState().syncActivity.pendingEvents).toEqual(
        snapshot.pendingEvents,
      );
    });
  });

  describe("in-flight events", () => {
    it("records and clears the batch being submitted", () => {
      let state = reducer(initialState, setEventsInFlight(["a", "b"]));
      expect(state.inFlightEventIds).toEqual(["a", "b"]);

      state = reducer(state, setEventsInFlight([]));
      expect(state.inFlightEventIds).toEqual([]);
    });
  });

  describe("completed events", () => {
    it("logs an event that has left the queue", () => {
      let state = reducer(initialState, snapshotOf([makeEvent("event-1")]));
      state = reducer(state, snapshotOf([]));

      expect(state.completedEvents).toHaveLength(1);
      expect(state.completedEvents[0].id).toBe("event-1");
      expect(state.completedEvents[0].completedAt).toBeGreaterThan(0);
      expect(state.pendingEvents).toEqual([]);
    });

    it("leaves outstanding events out of the log", () => {
      const event = makeEvent("event-1");
      let state = reducer(initialState, snapshotOf([event]));
      state = reducer(state, snapshotOf([event]));

      expect(state.completedEvents).toEqual([]);
    });

    it("does not backfill the log from the first snapshot of a session", () => {
      const state = reducer(initialState, snapshotOf([makeEvent("event-1")]));

      expect(state.completedEvents).toEqual([]);
    });

    it("skips read-state bookkeeping events", () => {
      const seen = makeEvent("event-1", {
        type: PendingEventType.SourceConversationSeen,
      });
      let state = reducer(
        initialState,
        snapshotOf([seen, makeEvent("event-2")]),
      );
      state = reducer(state, snapshotOf([]));

      expect(state.completedEvents.map((event) => event.id)).toEqual([
        "event-2",
      ]);
    });

    it("logs across snapshots, newest first", () => {
      let state = reducer(
        initialState,
        snapshotOf([makeEvent("event-1"), makeEvent("event-2")]),
      );
      state = reducer(state, snapshotOf([makeEvent("event-2")]));
      state = reducer(state, snapshotOf([]));

      expect(state.completedEvents.map((event) => event.id)).toEqual([
        "event-2",
        "event-1",
      ]);
    });

    it("keeps the newest first and caps the log", () => {
      const events = Array.from(
        { length: COMPLETED_EVENTS_LIMIT + 2 },
        (_, i) => makeEvent(`event-${i}`),
      );
      let state = reducer(initialState, snapshotOf(events));
      state = reducer(state, snapshotOf([]));

      expect(state.completedEvents).toHaveLength(COMPLETED_EVENTS_LIMIT);
      expect(state.completedEvents[0].id).toEqual(
        `event-${COMPLETED_EVENTS_LIMIT + 1}`,
      );
    });

    it("is exposed to the sidebar and clearable", () => {
      let state = reducer(initialState, snapshotOf([makeEvent("event-1")]));
      state = reducer(state, snapshotOf([]));

      expect(selectCompletedEvents(stateWith(state))).toHaveLength(1);
      expect(reducer(state, clearCompletedEvents()).completedEvents).toEqual(
        [],
      );
    });
  });

  describe("reset", () => {
    it("clears everything on sign out", () => {
      const populated: SyncActivityState = {
        ...initialState,
        downloads: { "item-1": makeDownload("item-1", FetchStatus.Paused) },
        pendingEvents: [makeEvent("event-1")],
        inFlightEventIds: ["event-1"],
        completedEvents: [{ ...makeEvent("event-0"), completedAt: 1000 }],
      };

      const state = reducer(populated, setUnauth.fulfilled(undefined, "", ""));
      expect(state).toEqual(initialState);
    });

    it("clears recents on request", () => {
      const populated: SyncActivityState = {
        ...initialState,
        recentDownloads: [makeDownload("item-1", FetchStatus.Complete)],
      };

      expect(
        reducer(populated, clearRecentDownloads()).recentDownloads,
      ).toEqual([]);
    });
  });

  describe("pending event display status", () => {
    it("reports an event in the current batch as sending", () => {
      const state = stateWith({
        pendingEvents: [makeEvent("event-1")],
        inFlightEventIds: ["event-1"],
      });

      expect(selectPendingEventActivity(state)[0].displayStatus).toBe(
        PendingEventDisplayStatus.SENDING,
      );
    });

    it("reports an unsubmitted event as queued", () => {
      const state = stateWith({ pendingEvents: [makeEvent("event-1")] });

      expect(selectPendingEventActivity(state)[0].displayStatus).toBe(
        PendingEventDisplayStatus.QUEUED,
      );
    });

    it.each([
      EventStatus.BadRequest,
      EventStatus.NotFound,
      EventStatus.Conflict,
      EventStatus.NotImplemented,
    ])("reports status %s as needing attention", (lastEventStatus) => {
      const state = stateWith({
        pendingEvents: [makeEvent("event-1", { lastEventStatus })],
      });

      expect(selectPendingEventActivity(state)[0].displayStatus).toBe(
        PendingEventDisplayStatus.NEEDS_ATTENTION,
      );
    });

    it.each([EventStatus.Processing, EventStatus.AlreadyReported])(
      "treats in-progress status %s as still queued",
      (lastEventStatus) => {
        // These are resubmitted until the server confirms them, so they are
        // not something the journalist has to act on.
        const state = stateWith({
          pendingEvents: [
            makeEvent("event-1", { lastEventStatus, retryAttempts: 2 }),
          ],
        });

        expect(selectPendingEventActivity(state)[0].displayStatus).toBe(
          PendingEventDisplayStatus.QUEUED,
        );
      },
    );
  });

  describe("download display status", () => {
    it.each([
      [FetchStatus.DownloadInProgress, DownloadDisplayStatus.DOWNLOADING],
      [FetchStatus.DecryptionInProgress, DownloadDisplayStatus.DECRYPTING],
      [FetchStatus.Paused, DownloadDisplayStatus.STOPPED],
      [FetchStatus.Initial, DownloadDisplayStatus.QUEUED],
      [
        FetchStatus.FailedDownloadRetryable,
        DownloadDisplayStatus.NEEDS_ATTENTION,
      ],
      [FetchStatus.FailedTerminal, DownloadDisplayStatus.NEEDS_ATTENTION],
    ])("maps fetch status %s to %s", (fetchStatus, expected) => {
      const state = stateWith({
        downloads: { "item-1": makeDownload("item-1", fetchStatus) },
      });

      expect(selectDownloadActivity(state)[0].displayStatus).toBe(expected);
    });
  });

  describe("selectNeedsAttentionCount", () => {
    it("counts failed events and failed downloads together", () => {
      const state = stateWith({
        pendingEvents: [
          makeEvent("event-1", { lastEventStatus: EventStatus.Conflict }),
          makeEvent("event-2"),
        ],
        downloads: {
          "item-1": makeDownload("item-1", FetchStatus.FailedTerminal),
          "item-2": makeDownload("item-2", FetchStatus.DownloadInProgress),
        },
      });

      expect(selectNeedsAttentionCount(state)).toBe(2);
    });

    it("does not count a paused download, which the user chose", () => {
      const state = stateWith({
        downloads: { "item-1": makeDownload("item-1", FetchStatus.Paused) },
      });

      expect(selectNeedsAttentionCount(state)).toBe(0);
    });
  });

  describe("selectSyncSummary", () => {
    it("says syncing while a download is in flight, even between syncs", () => {
      const state = stateWith({
        downloads: {
          "item-1": makeDownload("item-1", FetchStatus.DownloadInProgress),
        },
      });

      expect(selectHasActivityInFlight(state)).toBe(true);
      expect(selectSyncSummary(state)).toBe(SyncActivity.SYNCING);
    });

    it("says syncing while an event batch is being submitted", () => {
      const state = stateWith({ inFlightEventIds: ["event-1"] });

      expect(selectSyncSummary(state)).toBe(SyncActivity.SYNCING);
    });

    it("needs attention when a successful sync left a failure behind", () => {
      const state = stateWith(
        {
          downloads: {
            "item-1": makeDownload("item-1", FetchStatus.FailedTerminal),
          },
        },
        { lastSyncStarted: 1000, lastSyncFinished: 2000 },
      );

      expect(selectSyncSummary(state)).toBe(SyncActivity.NEEDS_ATTENTION);
    });

    it("is caught up when nothing is outstanding", () => {
      const state = stateWith(
        {},
        { lastSyncStarted: 1000, lastSyncFinished: 2000 },
      );

      expect(selectSyncSummary(state)).toBe(SyncActivity.UP_TO_DATE);
    });

    it("prefers syncing over attention when a retry is under way", () => {
      const state = stateWith(
        {
          pendingEvents: [
            makeEvent("event-1", { lastEventStatus: EventStatus.Conflict }),
          ],
        },
        { lastSyncStarted: 3000, lastSyncFinished: 2000 },
      );

      expect(selectSyncSummary(state)).toBe(SyncActivity.SYNCING);
    });
  });

  describe("selectRecentDownloads", () => {
    it("returns recents newest first", () => {
      const state = stateWith({
        recentDownloads: [
          makeDownload("item-2", FetchStatus.Complete),
          makeDownload("item-1", FetchStatus.Complete),
        ],
      });

      expect(selectRecentDownloads(state).map((d) => d.itemUuid)).toEqual([
        "item-2",
        "item-1",
      ]);
    });
  });
});
