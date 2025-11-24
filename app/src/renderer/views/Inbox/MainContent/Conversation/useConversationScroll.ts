import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import type { MutableRefObject } from "react";
import type { Item, SourceWithItems } from "../../../../../types";
import { useAppDispatch, useAppSelector } from "../../../../hooks";
import {
  initializeConversationIndicator,
  markConversationLastSeen,
  selectConversationLastSeen,
} from "../../../../features/sources/sourcesSlice";

const NEW_MESSAGE_SCROLL_OFFSET = 150;
const NEW_MESSAGE_SEEN_THRESHOLD = 12;

type PendingScrollTarget = "divider" | "bottom" | null;

export interface ConversationScrollState {
  scrollContainerRef: MutableRefObject<HTMLDivElement | null>;
  dividerRef: MutableRefObject<HTMLDivElement | null>;
  dividerItemUuid: string | null;
  hasItems: boolean;
  oldItems: Item[];
  newItems: Item[];
  acknowledgeNewMessages: () => void;
}

export function useConversationScroll(
  sourceWithItems: SourceWithItems | null,
): ConversationScrollState {
  const dispatch = useAppDispatch();
  const scrollContainerRef = useRef<HTMLDivElement>(null);
  const dividerRef = useRef<HTMLDivElement | null>(null);
  const [dividerItemUuid, setDividerItemUuid] = useState<string | null>(null);
  const sourceUuidRef = useRef<string | null>(null);
  const itemCountRef = useRef<number>(0);
  const dividerUuidRef = useRef<string | null>(null);
  const pendingScrollTargetRef = useRef<PendingScrollTarget>(null);
  const [_isAutoScrolling, setIsAutoScrollingState] = useState(false);
  const isAutoScrollingValueRef = useRef(false);
  const setIsAutoScrolling = useCallback(
    (nextValue: boolean) => {
      isAutoScrollingValueRef.current = nextValue;
      setIsAutoScrollingState(nextValue);
    },
    [setIsAutoScrollingState],
  );

  const activeSourceUuid = sourceWithItems?.uuid ?? null;
  const journalistUUID = useAppSelector(
    (state) => state.session.authData?.journalistUUID ?? null,
  );
  const lastSeenInteractionCount = useAppSelector((state) =>
    activeSourceUuid
      ? selectConversationLastSeen(state, activeSourceUuid)
      : undefined,
  );

  const items = useMemo<Item[]>(
    () => (sourceWithItems ? sourceWithItems.items : []),
    [sourceWithItems],
  );
  const itemCount = items.length;
  const hasItems = itemCount > 0;
  const latestInteractionCount = useMemo(() => {
    return sourceWithItems?.items.at(-1)?.data.interaction_count ?? null;
  }, [sourceWithItems?.items]);

  const historicalLastSeenInteractionCount = useMemo(() => {
    if (!sourceWithItems) {
      return null;
    }

    let maxSeen: number | null = null;
    for (const item of sourceWithItems.items) {
      const interaction = item.data.interaction_count;
      if (interaction == null) {
        continue;
      }

      let hasBeenSeen = false;
      if (journalistUUID) {
        hasBeenSeen = item.data.seen_by.includes(journalistUUID);
      } else if (item.data.kind !== "reply") {
        hasBeenSeen = item.data.is_read;
      } else {
        hasBeenSeen = true;
      }

      if (!hasBeenSeen) {
        continue;
      }

      if (maxSeen === null || interaction > maxSeen) {
        maxSeen = interaction;
      }
    }

    return maxSeen;
  }, [journalistUUID, sourceWithItems]);

  const initialLastSeenInteractionCount = useMemo(() => {
    if (historicalLastSeenInteractionCount !== null) {
      return historicalLastSeenInteractionCount;
    }
    return latestInteractionCount;
  }, [historicalLastSeenInteractionCount, latestInteractionCount]);

  useEffect(() => {
    if (!sourceWithItems || lastSeenInteractionCount !== undefined) {
      return;
    }
    dispatch(
      initializeConversationIndicator({
        sourceUuid: sourceWithItems.uuid,
        lastSeenInteractionCount: initialLastSeenInteractionCount,
      }),
    );
  }, [
    dispatch,
    initialLastSeenInteractionCount,
    lastSeenInteractionCount,
    sourceWithItems,
  ]);

  useEffect(() => {
    if (!sourceWithItems) {
      setDividerItemUuid(null);
      return;
    }

    if (lastSeenInteractionCount === undefined || items.length === 0) {
      setDividerItemUuid(null);
      return;
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

    setDividerItemUuid(firstNewItem ? firstNewItem.uuid : null);
  }, [items, lastSeenInteractionCount, sourceWithItems]);

  useEffect(() => {
    if (!sourceWithItems) {
      dividerUuidRef.current = null;
      sourceUuidRef.current = null;
      itemCountRef.current = 0;
      pendingScrollTargetRef.current = null;
      return;
    }

    const prevSourceUuid = sourceUuidRef.current;
    const prevCount = itemCountRef.current;

    if (prevSourceUuid !== sourceWithItems.uuid) {
      pendingScrollTargetRef.current = dividerItemUuid ? "divider" : "bottom";
    } else if (dividerItemUuid && dividerItemUuid !== dividerUuidRef.current) {
      pendingScrollTargetRef.current = "divider";
    } else if (itemCount > prevCount && !dividerItemUuid) {
      pendingScrollTargetRef.current = "bottom";
    }

    sourceUuidRef.current = sourceWithItems.uuid;
    itemCountRef.current = itemCount;
    dividerUuidRef.current = dividerItemUuid;
  }, [dividerItemUuid, itemCount, sourceWithItems]);

  const scrollToDivider = useCallback(() => {
    const scrollEl = scrollContainerRef.current;
    const dividerEl = dividerRef.current;
    if (!scrollEl || !dividerEl) {
      return false;
    }
    const target = Math.max(dividerEl.offsetTop - NEW_MESSAGE_SCROLL_OFFSET, 0);
    scrollEl.scrollTop = target;
    return true;
  }, []);

  const scrollToBottom = useCallback(() => {
    const scrollEl = scrollContainerRef.current;
    if (!scrollEl) {
      return false;
    }
    scrollEl.scrollTop = scrollEl.scrollHeight;
    return true;
  }, []);

  const scheduleAutoScrollReset = useCallback(() => {
    const reset = () => setIsAutoScrolling(false);

    if (typeof window !== "undefined" && window.requestAnimationFrame) {
      window.requestAnimationFrame(reset);
    } else {
      setTimeout(reset, 0);
    }
  }, [setIsAutoScrolling]);

  const acknowledgeNewMessages = useCallback(() => {
    if (!sourceWithItems) {
      return;
    }
    if (latestInteractionCount === null) {
      return;
    }
    dispatch(
      markConversationLastSeen({
        sourceUuid: sourceWithItems.uuid,
        interactionCount: latestInteractionCount,
      }),
    );
  }, [dispatch, latestInteractionCount, sourceWithItems]);

  useEffect(() => {
    const target = pendingScrollTargetRef.current;
    if (!target || !hasItems) {
      return;
    }

    setIsAutoScrolling(true);

    if (target === "divider" && dividerItemUuid && scrollToDivider()) {
      pendingScrollTargetRef.current = null;
      scheduleAutoScrollReset();
      return;
    }

    if (target === "bottom" && scrollToBottom()) {
      pendingScrollTargetRef.current = null;
      scheduleAutoScrollReset();
      return;
    }

    setIsAutoScrolling(false);
  }, [
    dividerItemUuid,
    hasItems,
    itemCount,
    scheduleAutoScrollReset,
    setIsAutoScrolling,
    scrollToBottom,
    scrollToDivider,
  ]);

  useEffect(() => {
    const scrollEl = scrollContainerRef.current;
    if (!scrollEl || !dividerItemUuid) {
      return;
    }

    const handleScroll = () => {
      if (isAutoScrollingValueRef.current) {
        return;
      }
      const distanceToBottom =
        scrollEl.scrollHeight - (scrollEl.scrollTop + scrollEl.clientHeight);
      if (distanceToBottom <= NEW_MESSAGE_SEEN_THRESHOLD) {
        acknowledgeNewMessages();
      }
    };

    scrollEl.addEventListener("scroll", handleScroll);
    return () => {
      scrollEl.removeEventListener("scroll", handleScroll);
    };
  }, [acknowledgeNewMessages, dividerItemUuid]);

  const { oldItems, newItems } = useMemo(() => {
    if (!dividerItemUuid) {
      return { oldItems: items, newItems: [] as typeof items };
    }

    const dividerIndex = items.findIndex(
      (item) => item.uuid === dividerItemUuid,
    );
    if (dividerIndex === -1) {
      return { oldItems: items, newItems: [] as typeof items };
    }

    return {
      oldItems: items.slice(0, dividerIndex),
      newItems: items.slice(dividerIndex),
    };
  }, [dividerItemUuid, items]);

  return {
    scrollContainerRef,
    dividerRef,
    dividerItemUuid,
    hasItems,
    oldItems,
    newItems,
    acknowledgeNewMessages,
  };
}

export default useConversationScroll;
