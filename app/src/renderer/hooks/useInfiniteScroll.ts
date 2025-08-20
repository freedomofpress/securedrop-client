import { useState, useCallback, useRef, useEffect } from "react";
import type { Source as SourceType } from "../../types";

const PAGE_SIZE = 20;
const VIRTUAL_WINDOW_SIZE = 100; // Keep 100 items in memory

interface UseInfiniteScrollParams {
  searchTerm: string;
  filter: "all" | "read" | "unread" | "starred" | "unstarred";
  sortedAsc: boolean;
}

interface UseInfiniteScrollReturn {
  sources: SourceType[];
  loading: boolean;
  hasMore: boolean;
  totalCount: number;
  containerRef: React.RefObject<HTMLDivElement | null>;
  resetPagination: () => void;
}

export function useInfiniteScroll(
  params: UseInfiniteScrollParams,
): UseInfiniteScrollReturn {
  const [sources, setSources] = useState<SourceType[]>([]);
  const [loading, setLoading] = useState(false);
  const [totalCount, setTotalCount] = useState(0);
  const [currentOffset, setCurrentOffset] = useState(0);
  const [hasMore, setHasMore] = useState(true);

  // Track if we've loaded all data
  const [allDataLoaded, setAllDataLoaded] = useState(false);

  const containerRef = useRef<HTMLDivElement>(null);
  const isLoadingRef = useRef(false);
  const lastParamsRef = useRef(params);

  // Reset pagination when filter params change
  const resetPagination = useCallback(() => {
    setSources([]);
    setCurrentOffset(0);
    setHasMore(true);
    setTotalCount(0);
    setAllDataLoaded(false);
  }, []);

  // Load sources for a specific offset
  const loadSources = useCallback(
    async (offset: number, append: boolean = true) => {
      if (isLoadingRef.current) return;

      isLoadingRef.current = true;
      setLoading(true);

      try {
        // Use the current params from the ref to avoid stale closures
        const currentParams = lastParamsRef.current;
        const [sourcesResult, countResult] = await Promise.all([
          window.electronAPI.getSources({
            ...currentParams,
            limit: PAGE_SIZE,
            offset,
          }),
          window.electronAPI.getSourcesCount(currentParams),
        ]);

        setTotalCount(countResult);

        if (append) {
          setSources((prev) => {
            // Create a set to track existing sources by UUID to prevent duplicates
            const existingSourceIds = new Set(
              prev.map((source) => source.uuid),
            );

            // Filter out any sources that already exist
            const uniqueNewSources = sourcesResult.filter(
              (source) => !existingSourceIds.has(source.uuid),
            );

            const newSources = [...prev, ...uniqueNewSources];

            // Implement simple virtual window: keep only VIRTUAL_WINDOW_SIZE items
            // Always keep the most recent items
            if (newSources.length > VIRTUAL_WINDOW_SIZE) {
              return newSources.slice(-VIRTUAL_WINDOW_SIZE);
            }

            return newSources;
          });
        } else {
          setSources(sourcesResult);
        }

        const hasMoreData = offset + PAGE_SIZE < countResult;
        setHasMore(hasMoreData);
        setCurrentOffset(offset + PAGE_SIZE);

        // Check if we've loaded all available data
        if (!hasMoreData) {
          setAllDataLoaded(true);
        }
      } catch (error) {
        console.error("Failed to load sources:", error);
      } finally {
        setLoading(false);
        isLoadingRef.current = false;
      }
    },
    [], // Remove params dependency to prevent recreation
  );

  // Check if params changed and reset if needed, then load initial data
  useEffect(() => {
    const paramsChanged =
      lastParamsRef.current.searchTerm !== params.searchTerm ||
      lastParamsRef.current.filter !== params.filter ||
      lastParamsRef.current.sortedAsc !== params.sortedAsc;

    if (paramsChanged || sources.length === 0) {
      lastParamsRef.current = params;

      if (paramsChanged) {
        resetPagination();
      }

      // Load the initial data
      if (!isLoadingRef.current) {
        loadSources(0, false);
      }
    }
  }, [
    params.searchTerm,
    params.filter,
    params.sortedAsc,
    sources.length,
    resetPagination,
  ]);

  // Load more sources when scrolling down
  const loadMore = useCallback(() => {
    if (hasMore && !loading && !allDataLoaded) {
      loadSources(currentOffset);
    }
  }, [hasMore, loading, currentOffset, allDataLoaded]);

  // Scroll event handler - simple infinite scroll (one direction only)
  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;

    const handleScroll = () => {
      const { scrollTop, scrollHeight, clientHeight } = container;
      const scrollPercentage = scrollTop / (scrollHeight - clientHeight);

      // Load more when near bottom (80%) and we have more data
      if (scrollPercentage > 0.8 && hasMore && !loading && !allDataLoaded) {
        loadMore();
      }
    };

    container.addEventListener("scroll", handleScroll, { passive: true });
    return () => container.removeEventListener("scroll", handleScroll);
  }, [hasMore, loading, loadMore, allDataLoaded]);

  return {
    sources,
    loading,
    hasMore,
    totalCount,
    containerRef,
    resetPagination,
  };
}
