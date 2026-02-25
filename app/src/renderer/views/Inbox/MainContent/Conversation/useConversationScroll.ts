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

const NEW_MESSAGE_SCROLL_OFFSET = 150;
const NEW_MESSAGE_SEEN_THRESHOLD = 12;

type PendingScrollTarget = "divider" | "bottom" | null;

export interface ConversationScrollState {
  listRef: (api: ListImperativeAPI | null) => void;
  dynamicRowHeight: DynamicRowHeight;
  dividerIndex: number | null;
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
  const [listAPI, listRef] = useListCallbackRef();
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
  const dynamicRowHeight = useDynamicRowHeight({
    defaultRowHeight: 100,
    key: activeSourceUuid ?? undefined,
  });

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

  const dividerItemUuid = useMemo(() => {
    if (!sourceWithItems) {
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

  const { oldItems, newItems } = useMemo(() => {
    if (!dividerItemUuid) {
      return { oldItems: items, newItems: [] as typeof items };
    }

    const idx = items.findIndex((item) => item.uuid === dividerItemUuid);
    if (idx === -1) {
      return { oldItems: items, newItems: [] as typeof items };
    }

    return {
      oldItems: items.slice(0, idx),
      newItems: items.slice(idx),
    };
  }, [dividerItemUuid, items]);

  const dividerIndex = dividerItemUuid !== null ? oldItems.length : null;

  const scrollToDivider = useCallback(() => {
    if (!listAPI || dividerIndex === null) {
      return false;
    }
    const el = listAPI.element;
    if (!el) {
      return false;
    }
    let offset = 0;
    for (let i = 0; i < dividerIndex; i++) {
      offset +=
        dynamicRowHeight.getRowHeight(i) ??
        dynamicRowHeight.getAverageRowHeight();
    }
    el.scrollTo({ top: Math.max(0, offset - NEW_MESSAGE_SCROLL_OFFSET) });
    return true;
  }, [listAPI, dividerIndex, dynamicRowHeight]);

  const scrollToBottom = useCallback(() => {
    if (!listAPI) {
      return false;
    }
    const totalRows =
      oldItems.length + (dividerIndex !== null ? 1 : 0) + newItems.length;
    if (totalRows === 0) {
      return false;
    }
    listAPI.scrollToRow({ index: totalRows - 1, align: "end" });
    return true;
  }, [listAPI, oldItems.length, newItems.length, dividerIndex]);

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

    // TODO: we shouldn't set state in an effect
    // eslint-disable-next-line react-hooks/set-state-in-effect
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
    const el = listAPI?.element;
    if (!el || !dividerItemUuid) {
      return;
    }
    const handleScroll = () => {
      if (isAutoScrollingValueRef.current) {
        return;
      }
      const distanceToBottom =
        el.scrollHeight - (el.scrollTop + el.clientHeight);
      if (distanceToBottom <= NEW_MESSAGE_SEEN_THRESHOLD) {
        acknowledgeNewMessages();
      }
    };
    el.addEventListener("scroll", handleScroll);
    return () => el.removeEventListener("scroll", handleScroll);
  }, [listAPI, acknowledgeNewMessages, dividerItemUuid]);

  return {
    listRef: listRef as (api: ListImperativeAPI | null) => void,
    dynamicRowHeight,
    dividerIndex,
    dividerItemUuid,
    hasItems,
    oldItems,
    newItems,
    acknowledgeNewMessages,
  };
}

export default useConversationScroll;
