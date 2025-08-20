import { useState, useCallback, useRef, useEffect } from "react";
import type { Source as SourceType } from "../../types";

const PAGE_SIZE = 100;

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
  const [currentPage, setCurrentPage] = useState(0);
  const [hasMore, setHasMore] = useState(true);

  const containerRef = useRef<HTMLDivElement>(null);
  const isLoadingRef = useRef(false);
  const lastParamsRef = useRef(params);
  const loadedPagesRef = useRef<Set<number>>(new Set());

  // Reset pagination when filter params change
  const resetPagination = useCallback(() => {
    setSources([]);
    setCurrentPage(0);
    setHasMore(true);
    setTotalCount(0);
    loadedPagesRef.current.clear();
  }, []);

  // Load sources for a specific page
  const loadSources = useCallback(
    async (page: number, append = true) => {
      if (isLoadingRef.current) return;

      // For append operations, check if we've already loaded this page
      if (append && loadedPagesRef.current.has(page)) {
        console.log(`Page ${page} already loaded, skipping`);
        return;
      }

      console.log(`Loading page ${page}, append: ${append}`);
      isLoadingRef.current = true;
      setLoading(true);

      try {
        const offset = page * PAGE_SIZE;

        // Get sources and total count in parallel
        const [sourcesResult, totalResult] = await Promise.all([
          window.electronAPI?.getSources({
            searchTerm: params.searchTerm,
            filter: params.filter,
            sortedAsc: params.sortedAsc,
            limit: PAGE_SIZE,
            offset,
          }),
          window.electronAPI?.getSourcesCount({
            searchTerm: params.searchTerm,
            filter: params.filter,
          }),
        ]);

        if (sourcesResult) {
          const newSources = sourcesResult;
          const total = totalResult || 0;
          console.log(
            `Loaded ${newSources.length} sources from page ${page}, total: ${total}`,
          );
          setTotalCount(total);

          setSources((prev) => {
            if (append) {
              // Mark this page as loaded
              loadedPagesRef.current.add(page);
              // Append new sources to the existing list, avoiding duplicates
              const existingUuids = new Set(prev.map((source) => source.uuid));
              const uniqueNewSources = newSources.filter(
                (source) => !existingUuids.has(source.uuid),
              );
              console.log(
                `Appending ${uniqueNewSources.length} unique sources (filtered ${newSources.length - uniqueNewSources.length} duplicates)`,
              );
              return [...prev, ...uniqueNewSources];
            } else {
              // Replace sources (for initial load or filter change)
              loadedPagesRef.current.clear();
              loadedPagesRef.current.add(page);
              return newSources;
            }
          });

          // Update pagination state
          const newOffset = offset + newSources.length;
          const hasMoreData = newOffset < total;
          console.log(
            `Setting hasMore to ${hasMoreData} (newOffset: ${newOffset}, total: ${total})`,
          );
          setHasMore(hasMoreData);
          if (append) {
            // Set currentPage to the next page we want to load
            setCurrentPage(page + 1);
            console.log(
              `Updated currentPage to ${page + 1} (next page to load)`,
            );
          } else {
            // For initial load, next page is 1
            setCurrentPage(1);
            console.log(
              `Set currentPage to 1 (next page to load after initial)`,
            );
          }
        }
      } catch (error) {
        console.error("Error loading sources:", error);
      } finally {
        isLoadingRef.current = false;
        setLoading(false);
      }
    },
    [params.searchTerm, params.filter, params.sortedAsc],
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
  }, [params, sources.length, resetPagination, loadSources]);

  // Load more sources when scrolling down
  const loadMore = useCallback(() => {
    console.log(
      `loadMore called: hasMore=${hasMore}, loading=${loading}, currentPage=${currentPage}`,
    );
    console.log(`loadedPages:`, Array.from(loadedPagesRef.current));
    if (hasMore && !loading) {
      loadSources(currentPage, true);
    }
  }, [hasMore, loading, currentPage, loadSources]);

  // Scroll event handler - infinite scroll
  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;

    const handleScroll = () => {
      const { scrollTop, scrollHeight, clientHeight } = container;
      const scrollPercentage = scrollTop / (scrollHeight - clientHeight);

      // Load more when near bottom (80%) and we have more data
      if (scrollPercentage > 0.8) {
        console.log(
          `Scroll threshold reached: ${scrollPercentage.toFixed(2)}, hasMore=${hasMore}, loading=${loading}`,
        );
        if (hasMore && !loading) {
          loadMore();
        }
      }
    };

    container.addEventListener("scroll", handleScroll, { passive: true });
    return () => container.removeEventListener("scroll", handleScroll);
  }, [hasMore, loading, loadMore]);

  return {
    sources,
    loading,
    hasMore,
    totalCount,
    containerRef,
    resetPagination,
  };
}
