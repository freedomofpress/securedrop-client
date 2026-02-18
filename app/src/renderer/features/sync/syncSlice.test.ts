import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { configureStore } from "@reduxjs/toolkit";
import { Source as SourceType, SyncStatus } from "../../../types";
import syncSlice, { syncMetadata } from "./syncSlice";
import sourcesSlice from "../sources/sourcesSlice";
import sessionSlice, { type AuthData } from "../session/sessionSlice";
import conversationSlice from "../conversation/conversationSlice";

function mockAuthData(token: string): AuthData {
  return {
    expiration: "",
    token,
    journalistUUID: "550e8400-e29b-41d4-a716-446655440000",
    journalistFirstName: null,
    journalistLastName: null,
  };
}

// Mock data matching the structure from test-component-setup.tsx
const mockSources: SourceType[] = [
  {
    uuid: "source-1",
    data: {
      fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
      is_starred: false,
      is_seen: false,
      has_attachment: false,
      journalist_designation: "multiplicative conditionality",
      last_updated: "2024-01-15T10:30:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-1",
    },
    isRead: false,
    hasAttachment: false,
    messagePreview: null,
  },
  {
    uuid: "source-2",
    data: {
      fingerprint: "1234ABCD5678EFGH9012IJKL3456MNOP7890QRST",
      is_starred: true,
      is_seen: true,
      has_attachment: true,
      journalist_designation: "piezoelectric crockery",
      last_updated: "2024-01-14T15:45:00Z",
      public_key:
        "-----BEGIN PGP PUBLIC KEY BLOCK-----\nVersion: GnuPG v1\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      uuid: "source-2",
    },
    isRead: true,
    hasAttachment: true,
    messagePreview: {
      kind: "message",
      plaintext: "Hello from source 2",
    },
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
    mockSyncMetadata.mockResolvedValue(SyncStatus.UPDATED);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("syncMetadata async thunk", () => {
    it("handles successful sync with auth token", async () => {
      const authToken = "test-auth-token";
      const action = syncMetadata(mockAuthData(authToken));
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledWith({
        authToken,
        hintedRecords: 0,
      });
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual(mockSources);
      expect(syncState.error).toBeNull();
      expect(syncState.lastFetchTime).toBeGreaterThan(0);
    });

    it("handles sync failure with invalid auth token", async () => {
      const errorMessage = "Authentication required";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      await (store.dispatch as any)(
        syncMetadata(mockAuthData("invalid-token")),
      );

      expect(mockSyncMetadata).toHaveBeenCalledWith({
        authToken: "invalid-token",
        hintedRecords: 0,
      });
      expect(mockGetSources).not.toHaveBeenCalled();

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.error).toBe(errorMessage);
    });

    it("handles sync metadata error", async () => {
      const errorMessage = "Failed to sync metadata";
      mockSyncMetadata.mockRejectedValue(new Error(errorMessage));

      const action = syncMetadata(mockAuthData("test-token"));
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.error).toBe(errorMessage);
    });

    it("handles getSources error after successful sync", async () => {
      const errorMessage = "Failed to get sources";
      mockGetSources.mockRejectedValue(new Error(errorMessage));

      const action = syncMetadata(mockAuthData("test-token"));
      await (store.dispatch as any)(action);

      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).toHaveBeenCalledTimes(1);

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual([]);
      expect(syncState.error).toBeNull(); // Sync succeeded, sources fetch failed
      expect(sourcesState.error).toBe(errorMessage); // Error is in sources slice
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
            error: null,
            lastFetchTime: null,
            loading: false,
            conversationIndicators: {},
          },
          sync: {
            error: null,
            lastFetchTime: null,
            status: null,
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

      await (store.dispatch as any)(syncMetadata(mockAuthData("test-token")));

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

      await (store.dispatch as any)(syncMetadata(mockAuthData("test-token")));

      // Should NOT have called getSourceWithItems since no active source
      expect(mockGetSourceWithItems).not.toHaveBeenCalled();

      // Sources should still be updated in the store
      const sourcesState = (store.getState() as any).sources;
      expect(sourcesState.sources).toEqual(mockSources);
    });

    it("handles network timeout error during sync", async () => {
      mockSyncMetadata.mockRejectedValue(new Error("Network timeout"));

      await (store.dispatch as any)(syncMetadata(mockAuthData("valid-token")));

      const syncState = (store.getState() as any).sync;
      const sourcesState = (store.getState() as any).sources;
      expect(syncState.error).toBe("Network timeout");
      expect(sourcesState.sources).toEqual([]);

      // syncMetadata should be called but getSources should not be called due to network failure
      expect(mockSyncMetadata).toHaveBeenCalledTimes(1);
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("handles non-Error rejection for syncMetadata", async () => {
      mockSyncMetadata.mockRejectedValue("String error");

      const action = syncMetadata(mockAuthData("test-token"));
      await (store.dispatch as any)(action);

      const syncState = (store.getState() as any).sync;
      expect(syncState.error).toBe("String error");
    });

    it("skips source fetch on no-update sync", async () => {
      mockSyncMetadata.mockResolvedValue(SyncStatus.NOT_MODIFIED);

      await (store.dispatch as any)(syncMetadata(mockAuthData("test-token")));

      // Should NOT have called getSourceWithItems
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("handles 403 forbidden response", async () => {
      mockSyncMetadata.mockResolvedValue(SyncStatus.FORBIDDEN);

      await (store.dispatch as any)(
        syncMetadata(mockAuthData("invalid-token")),
      );

      const syncState = (store.getState() as any).sync;
      expect(syncState.status).toBe(SyncStatus.FORBIDDEN);
      expect(syncState.error).toBeNull();
      expect(mockSyncMetadata).toHaveBeenCalledWith({
        authToken: "invalid-token",
        hintedRecords: 0,
      });
      expect(mockGetSources).not.toHaveBeenCalled();
    });

    it("stores sync status when sync is successful", async () => {
      mockSyncMetadata.mockResolvedValue(SyncStatus.UPDATED);

      await (store.dispatch as any)(syncMetadata(mockAuthData("test-token")));

      const syncState = (store.getState() as any).sync;
      expect(syncState.status).toBe(SyncStatus.UPDATED);
      expect(syncState.lastFetchTime).toBeGreaterThan(0);
    });

    it("stores NOT_MODIFIED status when no changes", async () => {
      mockSyncMetadata.mockResolvedValue(SyncStatus.NOT_MODIFIED);

      await (store.dispatch as any)(syncMetadata(mockAuthData("test-token")));

      const syncState = (store.getState() as any).sync;
      expect(syncState.status).toBe(SyncStatus.NOT_MODIFIED);
      expect(syncState.lastFetchTime).toBeGreaterThan(0);
    });
  });
});
