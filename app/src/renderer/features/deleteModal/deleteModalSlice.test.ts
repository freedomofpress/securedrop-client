import { describe, it, expect, vi, beforeEach } from "vitest";
import {
  openDeleteModal,
  closeDeleteModal,
  completeDeleteModal,
  selectDeleteModal,
  selectDeleteModalOpen,
  selectLastDeletedSources,
} from "./deleteModalSlice";
import { setUnauth } from "../session/sessionSlice";
import { setupStore } from "../../store";

// Use the real app store so the typed selectors (which expect the full
// RootState) resolve without casts; only the deleteModal slice is exercised.
function makeStore() {
  return setupStore();
}

describe("deleteModalSlice", () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Slice tests don't load the shared renderer setup, so provide the only
    // electronAPI method this slice touches. Individual tests reconfigure it
    // via vi.mocked(...).
    (window as any).electronAPI = {
      getSourceItemCounts: vi
        .fn()
        .mockResolvedValue({ messages: 0, files: 0, replies: 0 }),
    };
  });

  it("starts closed with no pending sources", () => {
    const store = makeStore();
    expect(selectDeleteModal(store.getState())).toEqual({
      open: false,
      pendingSources: [],
      loading: false,
      counts: { messages: 0, files: 0, replies: 0 },
      lastDeletedSources: [],
    });
  });

  it("opens with the requested sources and loads item counts", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockResolvedValue({
      messages: 3,
      files: 2,
      replies: 1,
    });

    const store = makeStore();
    const promise = store.dispatch(openDeleteModal(["source-1", "source-2"]));

    // Pending: modal is open and marked loading before counts resolve.
    const pending = selectDeleteModal(store.getState());
    expect(pending.open).toBe(true);
    expect(pending.loading).toBe(true);
    expect(pending.pendingSources).toEqual(["source-1", "source-2"]);

    await promise;

    const fulfilled = selectDeleteModal(store.getState());
    expect(fulfilled.loading).toBe(false);
    expect(fulfilled.counts).toEqual({ messages: 3, files: 2, replies: 1 });
    expect(window.electronAPI.getSourceItemCounts).toHaveBeenCalledWith([
      "source-1",
      "source-2",
    ]);
  });

  it("stays open with zeroed counts when fetching counts fails", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockRejectedValue(
      new Error("IPC failure"),
    );

    const store = makeStore();
    await store.dispatch(openDeleteModal(["source-1"]));

    const state = selectDeleteModal(store.getState());
    expect(state.open).toBe(true);
    expect(state.loading).toBe(false);
    expect(state.counts).toEqual({ messages: 0, files: 0, replies: 0 });
  });

  it("ignores requests with no sources", async () => {
    const store = makeStore();
    await store.dispatch(openDeleteModal([]));

    expect(selectDeleteModalOpen(store.getState())).toBe(false);
    expect(window.electronAPI.getSourceItemCounts).not.toHaveBeenCalled();
  });

  it("resets when the session ends (setUnauth)", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockResolvedValue({
      messages: 2,
      files: 1,
      replies: 0,
    });

    const store = makeStore();
    await store.dispatch(openDeleteModal(["source-1"]));
    expect(selectDeleteModalOpen(store.getState())).toBe(true);

    await store.dispatch(setUnauth(undefined));

    expect(selectDeleteModal(store.getState())).toEqual({
      open: false,
      pendingSources: [],
      loading: false,
      counts: { messages: 0, files: 0, replies: 0 },
      lastDeletedSources: [],
    });
  });

  it("records the acted-on sources and closes on completion", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockResolvedValue({
      messages: 1,
      files: 0,
      replies: 0,
    });

    const store = makeStore();
    await store.dispatch(openDeleteModal(["source-1", "source-2"]));

    store.dispatch(completeDeleteModal());

    const state = selectDeleteModal(store.getState());
    expect(state.open).toBe(false);
    expect(state.pendingSources).toEqual([]);
    // The completed sources are exposed so the source list can drop them from
    // its checkbox selection.
    expect(selectLastDeletedSources(store.getState())).toEqual([
      "source-1",
      "source-2",
    ]);
  });

  it("does not record acted-on sources when cancelled", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockResolvedValue({
      messages: 1,
      files: 0,
      replies: 0,
    });

    const store = makeStore();
    await store.dispatch(openDeleteModal(["source-1"]));

    store.dispatch(closeDeleteModal());

    expect(selectLastDeletedSources(store.getState())).toEqual([]);
  });

  it("resets to the initial state when closed", async () => {
    vi.mocked(window.electronAPI.getSourceItemCounts).mockResolvedValue({
      messages: 1,
      files: 0,
      replies: 0,
    });

    const store = makeStore();
    await store.dispatch(openDeleteModal(["source-1"]));
    expect(selectDeleteModalOpen(store.getState())).toBe(true);

    store.dispatch(closeDeleteModal());

    expect(selectDeleteModal(store.getState())).toEqual({
      open: false,
      pendingSources: [],
      loading: false,
      counts: { messages: 0, files: 0, replies: 0 },
      lastDeletedSources: [],
    });
  });
});
