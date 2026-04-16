import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import type { Item, SourceWithItems } from "../../../../../types";
import { useAppDispatch, useAppSelector } from "../../../../hooks";
import {
  initializeConversationIndicator,
  markConversationLastSeen,
  selectConversationLastSeen,
} from "../../../../features/sources/sourcesSlice";
import { useListCallbackRef, useDynamicRowHeight } from "react-window";
import type { ListImperativeAPI, DynamicRowHeight } from "react-window";

const NEW_MESSAGE_SEEN_THRESHOLD = 12;

type PendingScrollTarget =
  | "bottom"
  | { kind: "index"; rowIndex: number }
  | null;

export interface ConversationScrollState {
  listRef: (api: ListImperativeAPI | null) => void;
  scrollElement: HTMLElement | null;
  dynamicRowHeight: DynamicRowHeight;
  dividerIndex: number | null;
  dividerItemUuid: string | null;
  hasItems: boolean;
  heightsReady: boolean;
  oldItemIds: string[];
  newItemIds: string[];
  acknowledgeNewMessages: () => void;
  showNewMessagesButton: boolean;
  scrollToBottom: () => void;
}

export function useConversationScroll(
  sourceMetadata: Omit<SourceWithItems, "items"> | null,
  items: Item[],
): ConversationScrollState {
  const dispatch = useAppDispatch();
  const [listAPI, listRef] = useListCallbackRef();
  const sourceUuidRef = useRef<string | null>(null);
  const itemCountRef = useRef<number>(0);
  const firstItemUuidRef = useRef<string | null>(null);
  const pendingScrollTargetRef = useRef<PendingScrollTarget>(null);

  const [_isAutoScrolling, setIsAutoScrollingState] = useState(false);
  const isAutoScrollingValueRef = useRef(false);
  const isAtBottomRef = useRef(true);
  const [showNewMessagesButton, setShowNewMessagesButton] = useState(false);
  const setIsAutoScrolling = useCallback(
    (nextValue: boolean) => {
      isAutoScrollingValueRef.current = nextValue;
      setIsAutoScrollingState(nextValue);
    },
    [setIsAutoScrollingState],
  );

  const activeSourceUuid = sourceMetadata?.uuid ?? null;
  const dynamicRowHeight = useDynamicRowHeight({
    defaultRowHeight: 100,
    key: activeSourceUuid ?? undefined,
  });

  // Use heightsReady state to only set items to visible once the rows have
  // been sized
  const [heightsReady, setHeightsReady] = useState(false);
  useEffect(() => {
    // TODO: shouldn't set state in a hook
    // eslint-disable-next-line react-hooks/set-state-in-effect
    setHeightsReady(false);

    // First raf: initial render + useDynamicRowHeight measures row heights
    const raf1 = requestAnimationFrame(() => {
      // Second raf: rows are resized, so now we can display
      const raf2 = requestAnimationFrame(() => {
        setHeightsReady(true);
      });
      return () => cancelAnimationFrame(raf2);
    });
    return () => cancelAnimationFrame(raf1);
  }, [activeSourceUuid]);

  const itemCount = items.length;
  const hasItems = itemCount > 0;
  const lastSeenInteractionCount = useAppSelector((state) =>
    activeSourceUuid
      ? selectConversationLastSeen(state, activeSourceUuid)
      : undefined,
  );
  const latestInteractionCount = useMemo(() => {
    return items.at(-1)?.data.interaction_count ?? null;
  }, [items]);

  useEffect(() => {
    if (!sourceMetadata || lastSeenInteractionCount !== undefined) {
      return;
    }
    dispatch(
      initializeConversationIndicator({
        sourceUuid: sourceMetadata.uuid,
        // If lastSeenInteractionCount is null/undefined, fall back to latest interaction
        // count so we show most recent message on first-time open.
        lastSeenInteractionCount:
          sourceMetadata.lastSeenInteractionCount ?? latestInteractionCount,
      }),
    );
  }, [
    dispatch,
    lastSeenInteractionCount,
    latestInteractionCount,
    sourceMetadata,
  ]);

  // If there are new, unseen messages, get the UUID for the "new messages" divider
  const dividerItemUuid = useMemo(() => {
    if (!sourceMetadata) {
      return null;
    }

    if (lastSeenInteractionCount === undefined || items.length === 0) {
      return null;
    }

    const threshold =
      lastSeenInteractionCount === null ? -Infinity : lastSeenInteractionCount;
    const firstNewItem = items.find((item) => {
      if (item.data.kind === "reply") {
        return false;
      }
      const interaction = item.data.interaction_count ?? null;
      if (interaction === null) {
        return false;
      }
      return interaction > threshold;
    });

    return firstNewItem ? firstNewItem.uuid : null;
  }, [items, lastSeenInteractionCount, sourceMetadata]);

  const { oldItemIds, newItemIds } = useMemo(() => {
    if (!dividerItemUuid) {
      return { oldItemIds: items.map((i) => i.uuid), newItemIds: [] as string[] };
    }

    const idx = items.findIndex((item) => item.uuid === dividerItemUuid);
    if (idx === -1) {
      return { oldItemIds: items.map((i) => i.uuid), newItemIds: [] as string[] };
    }

    return {
      oldItemIds: items.slice(0, idx).map((i) => i.uuid),
      newItemIds: items.slice(idx).map((i) => i.uuid),
    };
  }, [dividerItemUuid, items]);

  const dividerIndex = dividerItemUuid !== null ? oldItemIds.length : null;

  // Set the scroll target:
  // If switching to this conversation and there is a new messages divider,
  // we scroll to the divider. If there are no new messages, we default to bottom.
  // On historical load, we restore the scroll by centering the last visible row
  useEffect(() => {
    if (!sourceMetadata) {
      sourceUuidRef.current = null;
      itemCountRef.current = 0;
      firstItemUuidRef.current = null;
      pendingScrollTargetRef.current = null;
      return;
    }

    const prevSourceUuid = sourceUuidRef.current;
    const prevCount = itemCountRef.current;
    const prevFirstItemUuid = firstItemUuidRef.current;
    const newFirstItemUuid = items[0]?.uuid ?? null;

    if (prevSourceUuid !== sourceMetadata.uuid) {
      pendingScrollTargetRef.current = dividerIndex
        ? { kind: "index", rowIndex: dividerIndex }
        : "bottom";
      isAtBottomRef.current = true;
      // eslint-disable-next-line react-hooks/set-state-in-effect
      setShowNewMessagesButton(false);
    } else if (itemCount > prevCount) {
      if (
        prevFirstItemUuid !== null &&
        newFirstItemUuid !== prevFirstItemUuid
      ) {
        // On historical load (prepends items to top), restore the scroll
        // position by scrolling to what was previously the first visible row.
        const numPrepended = itemCount - prevCount;
        pendingScrollTargetRef.current = {
          kind: "index",
          rowIndex: numPrepended,
        };
      } else if (prevCount > 0) {
        // New messages appended at the bottom while the user is scrolled up
        const lastItem = sourceWithItems.items.at(-1);

        if (lastItem?.data.kind === "reply") {
          // Auto-scroll to bottom if it is a user-sent reply
          pendingScrollTargetRef.current = "bottom";
        } else if (!isAtBottomRef.current) {
          // Otherwise, show the "new messages" button if we are not at the bottom
          setShowNewMessagesButton(true);
        }
      }
    }

    sourceUuidRef.current = sourceMetadata.uuid;
    itemCountRef.current = itemCount;
    firstItemUuidRef.current = newFirstItemUuid;
  }, [dividerIndex, dividerItemUuid, itemCount, sourceMetadata, items]);

  const scrollToRowWithRetry = useCallback(
    (index: number, align: "start" | "center" | "end", maxRetries: number) => {
      if (!listAPI) {
        return false;
      }
      const scroll = (attempt: number) => {
        listAPI.scrollToRow({ index, align, behavior: "instant" });
        if (attempt < maxRetries) {
          requestAnimationFrame(() => scroll(attempt + 1));
        }
      };
      requestAnimationFrame(() => scroll(1));
      return true;
    },
    [listAPI],
  );

  const scheduleAutoScrollReset = useCallback(() => {
    requestAnimationFrame(() => setIsAutoScrolling(false));
  }, [setIsAutoScrolling]);

  const acknowledgeNewMessages = useCallback(() => {
    if (!sourceMetadata) {
      return;
    }
    if (latestInteractionCount === null) {
      return;
    }
    dispatch(
      markConversationLastSeen({
        sourceUuid: sourceMetadata.uuid,
        interactionCount: latestInteractionCount,
      }),
    );
  }, [dispatch, latestInteractionCount, sourceMetadata]);

  useEffect(() => {
    const target = pendingScrollTargetRef.current;
    if (!target || !hasItems) {
      return;
    }

    let rowIndex: number;
    let align: "start" | "center" | "end";

    if (target === "bottom") {
      const totalRows =
        oldItemIds.length + (dividerIndex !== null ? 1 : 0) + newItemIds.length;
      if (totalRows === 0) {
        return;
      }
      rowIndex = totalRows - 1;
      align = "end";
    } else {
      rowIndex = target.rowIndex;
      align = "center";
    }

    // TODO: we shouldn't set state in an effect
    // eslint-disable-next-line react-hooks/set-state-in-effect
    setIsAutoScrolling(true);

    if (scrollToRowWithRetry(rowIndex, align, 5)) {
      pendingScrollTargetRef.current = null;
      scheduleAutoScrollReset();
      return;
    }

    setIsAutoScrolling(false);
  }, [
    dividerIndex,
    hasItems,
    itemCount,
    newItemIds.length,
    oldItemIds.length,
    scheduleAutoScrollReset,
    setIsAutoScrolling,
    scrollToRowWithRetry,
  ]);

  // Track whether the user is at the bottom to show/hide new messages button
  // and acknowledge newly seen messages
  useEffect(() => {
    const el = listAPI?.element;
    if (!el) {
      return;
    }
    const handleScroll = () => {
      if (isAutoScrollingValueRef.current) {
        return;
      }
      const distanceToBottom =
        el.scrollHeight - (el.scrollTop + el.clientHeight);
      isAtBottomRef.current = distanceToBottom <= NEW_MESSAGE_SEEN_THRESHOLD;
      if (isAtBottomRef.current) {
        if (dividerItemUuid) {
          acknowledgeNewMessages();
        }
        setShowNewMessagesButton(false);
      }
    };
    el.addEventListener("scroll", handleScroll);
    return () => el.removeEventListener("scroll", handleScroll);
  }, [listAPI, acknowledgeNewMessages, dividerItemUuid]);

  const scrollToBottom = useCallback(() => {
    const totalRows =
      oldItems.length + (dividerIndex !== null ? 1 : 0) + newItems.length;
    if (totalRows > 0) {
      scrollToRowWithRetry(totalRows - 1, "end", 3);
    }
    setShowNewMessagesButton(false);
  }, [dividerIndex, newItems.length, oldItems.length, scrollToRowWithRetry]);

  return {
    listRef: listRef as (api: ListImperativeAPI | null) => void,
    scrollElement: listAPI?.element ?? null,
    dynamicRowHeight,
    dividerIndex,
    dividerItemUuid,
    hasItems,
    heightsReady,
    oldItemIds,
    newItemIds,
    acknowledgeNewMessages,
    showNewMessagesButton,
    scrollToBottom,
  };
}

export default useConversationScroll;
