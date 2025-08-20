import { renderHook, act, waitFor } from "@testing-library/react";
import { expect, describe, it, vi, beforeEach, afterEach } from "vitest";
import { useInfiniteScroll } from "./useInfiniteScroll";
import type { Source as SourceType } from "../../types";

// Mock console.log to avoid noise in tests
const mockConsoleLog = vi.spyOn(console, "log").mockImplementation(() => {});

describe("useInfiniteScroll", () => {
  const mockGetSources = vi.fn();
  const mockGetSourcesCount = vi.fn();

  // Create mock sources for testing
  const createMockSources = (startId: number, count: number): SourceType[] => {
    return Array.from({ length: count }, (_, index) => ({
      uuid: `source-${startId + index}`,
      data: {
        fingerprint: `fingerprint-${startId + index}`,
        is_starred: false,
        journalist_designation: `source-${startId + index}`,
        last_updated: new Date().toISOString(),
        public_key: `key-${startId + index}`,
        uuid: `source-${startId + index}`,
      },
      isRead: false,
      hasAttachment: false,
      showMessagePreview: false,
      messagePreview: "",
    }));
  };

  beforeEach(() => {
    vi.clearAllMocks();

    // Reset console.log mock
    mockConsoleLog.mockClear();

    // Mock electronAPI
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    (window as any).electronAPI = {
      getSources: mockGetSources,
      getSourcesCount: mockGetSourcesCount,
    };

    // Default implementation: return paginated results
    mockGetSources.mockImplementation(({ offset = 0, limit = 100 }) => {
      const sources = createMockSources(offset, Math.min(limit, 1000 - offset));
      return Promise.resolve(sources);
    });

    mockGetSourcesCount.mockResolvedValue(1000);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("Initial loading", () => {
    it("should load initial sources on mount", async () => {
      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      // Initially should be in loading state
      expect(result.current.loading).toBe(true);
      expect(result.current.sources).toEqual([]);

      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledWith({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
          limit: 100,
          offset: 0,
        });
      });

      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
        expect(result.current.totalCount).toBe(1000);
        expect(result.current.hasMore).toBe(true);
        expect(result.current.loading).toBe(false);
      });
    });

    it("should set hasMore to false when all sources are loaded", async () => {
      mockGetSources.mockResolvedValue(createMockSources(0, 50));
      mockGetSourcesCount.mockResolvedValue(50);

      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      await waitFor(() => {
        expect(result.current.sources).toHaveLength(50);
        expect(result.current.totalCount).toBe(50);
        expect(result.current.hasMore).toBe(false);
      });
    });
  });

  describe("Parameter changes", () => {
    it("should reset and reload when search term changes", async () => {
      const { result, rerender } = renderHook(
        ({ searchTerm }) =>
          useInfiniteScroll({
            searchTerm,
            filter: "all",
            sortedAsc: false,
          }),
        {
          initialProps: { searchTerm: "" },
        },
      );

      // Wait for initial load
      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
      });

      // Clear mock calls from initial load
      mockGetSources.mockClear();

      // Change search term
      rerender({ searchTerm: "test" });

      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledWith({
          searchTerm: "test",
          filter: "all",
          sortedAsc: false,
          limit: 100,
          offset: 0,
        });
      });
    });

    it("should reset and reload when filter changes", async () => {
      const { result, rerender } = renderHook(
        ({ filter }) =>
          useInfiniteScroll({
            searchTerm: "",
            filter,
            sortedAsc: false,
          }),
        {
          initialProps: {
            filter: "all" as
              | "all"
              | "read"
              | "unread"
              | "starred"
              | "unstarred",
          },
        },
      );

      // Wait for initial load
      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
      });

      // Clear mock calls from initial load
      mockGetSources.mockClear();

      // Change filter
      rerender({
        filter: "unread" as "all" | "read" | "unread" | "starred" | "unstarred",
      });

      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledWith({
          searchTerm: "",
          filter: "unread",
          sortedAsc: false,
          limit: 100,
          offset: 0,
        });
      });
    });

    it("should reset and reload when sort order changes", async () => {
      const { result, rerender } = renderHook(
        ({ sortedAsc }) =>
          useInfiniteScroll({
            searchTerm: "",
            filter: "all",
            sortedAsc,
          }),
        {
          initialProps: { sortedAsc: false },
        },
      );

      // Wait for initial load
      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
      });

      // Clear mock calls from initial load
      mockGetSources.mockClear();

      // Change sort order
      rerender({ sortedAsc: true });

      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledWith({
          searchTerm: "",
          filter: "all",
          sortedAsc: true,
          limit: 100,
          offset: 0,
        });
      });
    });
  });

  describe("Reset pagination", () => {
    it("should reset pagination manually", async () => {
      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      // Wait for initial load
      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
      });

      // Reset pagination
      act(() => {
        result.current.resetPagination();
      });

      expect(result.current.sources).toEqual([]);
      expect(result.current.totalCount).toBe(0);
      expect(result.current.hasMore).toBe(true);
    });
  });

  describe("Error handling", () => {
    it("should handle getSources errors gracefully", async () => {
      mockGetSources.mockRejectedValue(new Error("Network error"));

      const consoleSpy = vi
        .spyOn(console, "error")
        .mockImplementation(() => {});

      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      await waitFor(() => {
        expect(consoleSpy).toHaveBeenCalledWith(
          "Error loading sources:",
          expect.any(Error),
        );
        expect(result.current.loading).toBe(false);
        expect(result.current.sources).toEqual([]);
      });

      consoleSpy.mockRestore();
    });
  });

  describe("Duplicate prevention", () => {
    it("should prevent duplicate sources when the same data is returned", async () => {
      // Mock getSources to return overlapping data
      mockGetSources.mockImplementation(({ offset = 0 }) => {
        if (offset === 0) {
          // First call: return sources 0-99
          return Promise.resolve(createMockSources(0, 100));
        } else if (offset === 100) {
          // Second call: return sources 50-149 (overlapping with first call)
          // This simulates a race condition or server issue where duplicate data is returned
          return Promise.resolve(createMockSources(50, 100));
        }
        return Promise.resolve([]);
      });

      mockGetSourcesCount.mockResolvedValue(200);

      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      // Wait for initial load (sources 0-99)
      await waitFor(() => {
        expect(result.current.sources).toHaveLength(100);
        expect(result.current.hasMore).toBe(true);
      });

      // Trigger load more to get overlapping data
      await act(async () => {
        result.current.loadMore?.();
      });

      // Wait for second load to complete
      await waitFor(() => {
        expect(mockGetSources).toHaveBeenCalledTimes(2);
      });

      // Should have 150 unique sources (0-149), not 200 with duplicates
      // Sources 0-49 from first call, sources 50-149 from second call
      // Duplicates 50-99 should be filtered out
      expect(result.current.sources).toHaveLength(150);

      // Verify no duplicates exist in the final list
      const uuids = result.current.sources.map((s) => s.uuid);
      const uniqueUuids = new Set(uuids);
      expect(uuids.length).toBe(uniqueUuids.size);

      // Verify we have the expected range of sources (0-149)
      const expectedUuids = Array.from(
        { length: 150 },
        (_, i) => `source-${i}`,
      );
      const actualUuids = uuids.sort();
      expect(actualUuids).toEqual(expectedUuids.sort());
    });
  });

  describe("Loading states", () => {
    it("should set loading to true during API calls", async () => {
      let resolveGetSources: (value: SourceType[]) => void;
      const getSourcesPromise = new Promise<SourceType[]>((resolve) => {
        resolveGetSources = resolve;
      });

      mockGetSources.mockReturnValue(getSourcesPromise);

      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      // Verify loading state
      expect(result.current.loading).toBe(true);

      // Resolve the promise
      act(() => {
        resolveGetSources!(createMockSources(0, 100));
      });

      await waitFor(() => {
        expect(result.current.loading).toBe(false);
      });
    });
  });

  describe("Pagination state", () => {
    it("should handle where no sources are returned", async () => {
      mockGetSources.mockResolvedValue([]);
      mockGetSourcesCount.mockResolvedValue(0);

      const { result } = renderHook(() =>
        useInfiniteScroll({
          searchTerm: "",
          filter: "all",
          sortedAsc: false,
        }),
      );

      await waitFor(() => {
        expect(result.current.sources).toHaveLength(0);
        expect(result.current.totalCount).toBe(0);
        expect(result.current.hasMore).toBe(false);
        expect(result.current.loading).toBe(false);
      });
    });
  });
});
