/* eslint-disable @typescript-eslint/no-explicit-any */
import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import type { Source as SourceType } from "../../../types";
import syncSlice, { syncMetadata } from "./syncSlice";
import sourcesSlice from "../sources/sourcesSlice";
import sessionSlice from "../session/sessionSlice";
import conversationSlice from "../conversation/conversationSlice";

// Mock data matching the structure from test-component-setup.tsx
const mockSources: SourceType[] = [
  {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      journalist_designation: "multiplicative conditionality",
      last_updated: "2024-01-15T10:30:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-1",
    },
    isRead: false,
    hasAttachment: false,
    showMessagePreview: false,
    messagePreview: "",
  },
  {
    uuid: "source-2",
    data: {
      fingerprint: "1234ABCD5678EFGH9012IJKL3456MNOP7890QRST",
      is_starred: true,
      journalist_designation: "piezoelectric crockery",
      last_updated: "2024-01-14T15:45:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-2",
    },
    isRead: true,
    hasAttachment: true,
    showMessagePreview: true,
    messagePreview: "Hello from source 2",
  },
];

describe("syncSlice", () => {
  let store: ReturnType<typeof configureStore>;
  const mockGetSources = vi.fn();
  const mockSyncMetadata = vi.fn();

  beforeEach(() => {
    // Create a test store with sources, session, conversations, and sync slices for proper typing
    store = configureStore({
      reducer: {
        sources: sourcesSlice,
        session: sessionSlice,
        conversation: conversationSlice,
        sync: syncSlice,
      },
    });

    // Reset mocks
    vi.clearAllMocks();

    // Mock electronAPI
    (window as any).electronAPI = {
      getSources: mockGetSources,
      syncMetadata: mockSyncMetadata,
      getSourceWithItems: vi.fn().mockResolvedValue({
        uuid: "source-1",
        data: mockSources[0].data,
        items: [],
      }),
    };

    // Default mock implementations
    mockGetSources.mockResolvedValue(mockSources);
    mockSyncMetadata.mockResolvedValue(undefined);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("syncMetadata async thunk", () => {
    it("handles successful sync with auth token", async () => {
      const authToken = "test-auth-token";
      const action = syncMetadata(authToken);
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledWith({ authToken });
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual(mockSources);
      expect(syncState.loading).toBe(false);
      expect(syncState.error).toBeNull();
      expect(syncState.lastFetchTime).toBeGreaterThan(0);
    });

    it("handles sync failure without auth token", async () => {
      const errorMessage = "Authentication required";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(syncMetadata(undefined));

      expect(mockSyncMetadata).toHaveBeenCalledWith({ authToken: undefined });
      expect(mockGetSources).not.toHaveBeenCalled();

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.loading).toBe(false);
      expect(syncState.error).toBe(errorMessage);
    });

    it("handles sync metadata error", async () => {
      const errorMessage = "Failed to sync metadata";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      const action = syncMetadata("test-token");
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.loading).toBe(false);
      expect(syncState.error).toBe(errorMessage);
    });

    it("handles getSources error after successful sync", async () => {
      const errorMessage = "Failed to get sources";
      mockGetSources.mockRejectedValue(new Error(errorMessage));

      const action = syncMetadata("test-token");
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.loading).toBe(false);
      expect(syncState.error).toBeNull(); // Sync succeeded, sources fetch failed
      expect(sourcesState.error).toBe(errorMessage); // Error is in sources slice
    });

    it("sets loading state during sync", async () => {
      // Create promises that we can control
      let resolveSyncMetadata!: () => void;
      let resolveGetSources!: (value: SourceType[]) => void;

      const syncMetadataPromise = new Promise<void>((resolve) => {
        resolveSyncMetadata = resolve;
      });
      const getSourcesPromise = new Promise<SourceType[]>((resolve) => {
        resolveGetSources = resolve;
      });

      mockSyncMetadata.mockReturnValue(syncMetadataPromise);
      mockGetSources.mockReturnValue(getSourcesPromise);

      const action = syncMetadata("test-token");
      const dispatchPromise = (store.dispatch as any)(action);

      // Check loading state is true while pending
      expect((store.getState() as any).sync.loading).toBe(true);
      expect((store.getState() as any).sync.error).toBeNull();

      // Resolve both promises
      resolveSyncMetadata!();
      resolveGetSources!(mockSources);
      await dispatchPromise;

      // Check loading state is false after completion
      expect((store.getState() as any).sync.loading).toBe(false);
    });

    it("fetches conversation for active source during sync", async () => {
      const activeSourceUuid = "source-1";

      // Set up store with active source
      store = configureStore({
        reducer: {
          sources: sourcesSlice,
          session: sessionSlice,
          conversation: conversationSlice,
          sync: syncSlice,
        },
        preloadedState: {
          sources: {
            sources: [],
            activeSourceUuid: activeSourceUuid,
            loading: false,
            error: null,
            starPendingStates: {},
          },
          sync: {
            loading: false,
            error: null,
            lastFetchTime: null,
          },
        },
      });

      // Mock getSourceWithItems for the active conversation
      const mockGetSourceWithItems = vi.fn();
      (window as any).electronAPI.getSourceWithItems = mockGetSourceWithItems;
      mockGetSourceWithItems.mockResolvedValue({
        uuid: activeSourceUuid,
        data: mockSources[0].data,
        items: [],
      });

      await (store.dispatch as any)(syncMetadata("test-token"));

      // Should have called getSourceWithItems for the active source only
      expect(mockGetSourceWithItems).toHaveBeenCalledWith(activeSourceUuid);
      expect(mockGetSourceWithItems).toHaveBeenCalledTimes(1);

      // Sources should be updated
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual(mockSources);
    });

    it("does not fetch conversations when no active source", async () => {
      const mockGetSourceWithItems = vi.fn();
      (window as any).electronAPI.getSourceWithItems = mockGetSourceWithItems;

      await (store.dispatch as any)(syncMetadata("test-token"));

      // Should NOT have called getSourceWithItems since no active source
      expect(mockGetSourceWithItems).not.toHaveBeenCalled();

      // Sources should still be updated in the store
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual(mockSources);
    });

    it("handles network timeout error during sync", async () => {
      mockSyncMetadata.mockRejectedValue(new Error("Network timeout"));

      await (store.dispatch as any)(syncMetadata("valid-token"));

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(syncState.error).toBe("Network timeout");
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.loading).toBe(false);

      // syncMetadata should be called but getSources should not be called due to network failure
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("handles non-Error rejection for syncMetadata", async () => {
      mockSyncMetadata.mockRejectedValue("String error");

      const action = syncMetadata("test-token");
      await (store.dispatch as any)(action);

      const syncState = (store.getState() as any).sync;
      expect(syncState.error).toBe("String error");
    });
  });
});
