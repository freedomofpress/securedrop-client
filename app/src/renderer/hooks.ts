import { useDispatch, useSelector, useStore } from "react-redux";
import { useEffect, useState, useCallback, useRef } from "react";
import type { AppDispatch, AppStore, RootState } from "./store";
import type { Source as SourceType } from "../types";

export const useAppDispatch = useDispatch.withTypes<AppDispatch>();
export const useAppSelector = useSelector.withTypes<RootState>();
export const useAppStore = useStore.withTypes<AppStore>();

export function useDebounce<T>(value: T, delay: number): T {
  const [debouncedValue, setDebouncedValue] = useState<T>(value);

  useEffect(() => {
    const handler = setTimeout(() => {
      setDebouncedValue(value);
    }, delay);

    return () => {
      clearTimeout(handler);
    };
  }, [value, delay]);

  return debouncedValue;
}

const PAGE_SIZE = 100;
const VIRTUAL_WINDOW_SIZE = 300; // Keep 300 items in memory

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

  // Track the virtual window boundaries
  const [windowStart, setWindowStart] = useState(0);

  const containerRef = useRef<HTMLDivElement>(null);
  const isLoadingRef = useRef(false);
  const lastParamsRef = useRef(params);

  // Reset pagination when filter params change
  const resetPagination = useCallback(() => {
    setSources([]);
    setCurrentOffset(0);
    setWindowStart(0);
    setHasMore(true);
    setTotalCount(0);
  }, []);

  // Check if params changed and reset if needed
  useEffect(() => {
    const paramsChanged =
      lastParamsRef.current.searchTerm !== params.searchTerm ||
      lastParamsRef.current.filter !== params.filter ||
      lastParamsRef.current.sortedAsc !== params.sortedAsc;

    if (paramsChanged) {
      lastParamsRef.current = params;
      resetPagination();
    }
  }, [params, resetPagination]);

  // Load sources for a specific offset
  const loadSources = useCallback(
    async (offset: number, append: boolean = true) => {
      if (isLoadingRef.current) return;

      isLoadingRef.current = true;
      setLoading(true);

      try {
        const [sourcesResult, countResult] = await Promise.all([
          window.electronAPI.getSources({
            ...params,
            limit: PAGE_SIZE,
            offset,
          }),
          window.electronAPI.getSourcesCount(params),
        ]);

        setTotalCount(countResult);

        if (append) {
          setSources((prev) => {
            const newSources = [...prev, ...sourcesResult];
            // Implement virtual window: keep only VIRTUAL_WINDOW_SIZE items
            if (newSources.length > VIRTUAL_WINDOW_SIZE) {
              const startIndex = Math.max(
                0,
                newSources.length - VIRTUAL_WINDOW_SIZE,
              );
              return newSources.slice(startIndex);
            }
            return newSources;
          });
        } else {
          setSources(sourcesResult);
        }

        setHasMore(offset + PAGE_SIZE < countResult);
        setCurrentOffset(offset + PAGE_SIZE);
      } catch (error) {
        console.error("Failed to load sources:", error);
      } finally {
        setLoading(false);
        isLoadingRef.current = false;
      }
    },
    [params],
  );

  // Load more sources when scrolling down
  const loadMore = useCallback(() => {
    if (hasMore && !loading) {
      loadSources(currentOffset);
    }
  }, [hasMore, loading, currentOffset, loadSources]);

  // Load earlier sources when scrolling up
  const loadEarlier = useCallback(() => {
    if (windowStart > 0 && !loading) {
      const newOffset = Math.max(0, windowStart - PAGE_SIZE);
      setWindowStart(newOffset);
      loadSources(newOffset, false);
    }
  }, [windowStart, loading, loadSources]);

  // Scroll event handler
  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;

    const handleScroll = () => {
      const { scrollTop, scrollHeight, clientHeight } = container;
      const scrollPercentage = scrollTop / (scrollHeight - clientHeight);

      // Load more when near bottom (90%)
      if (scrollPercentage > 0.9 && hasMore && !loading) {
        loadMore();
      }

      // Load earlier when near top (10%) and not at the beginning
      if (scrollPercentage < 0.1 && windowStart > 0 && !loading) {
        loadEarlier();
      }
    };

    container.addEventListener("scroll", handleScroll, { passive: true });
    return () => container.removeEventListener("scroll", handleScroll);
  }, [hasMore, loading, loadMore, loadEarlier, windowStart]);

  // Initial load
  useEffect(() => {
    if (sources.length === 0 && !loading) {
      loadSources(0, false);
    }
  }, [sources.length, loading, loadSources]);

  return {
    sources,
    loading,
    hasMore,
    totalCount,
    containerRef,
    resetPagination,
  };
}
