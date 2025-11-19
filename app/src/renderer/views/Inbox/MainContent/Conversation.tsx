import type { SourceWithItems } from "../../../../types";
import { toTitleCase } from "../../../utils";
import Item from "./Conversation/Item";
import NewMessagesDivider from "./Conversation/NewMessagesDivider";
import EmptyConversation from "./EmptyConversation";
import { Form, Input, Button } from "antd";
import { useTranslation } from "react-i18next";
import { useEffect, useRef, memo, useMemo, useCallback, useState } from "react";
import { useAppDispatch, useAppSelector } from "../../../hooks";
import {
  fetchSources,
  initializeConversationIndicator,
  markConversationLastSeen,
  selectConversationLastSeen,
} from "../../../features/sources/sourcesSlice";
import { fetchConversation } from "../../../features/conversation/conversationSlice";
import "./Conversation.css";

const NEW_MESSAGE_SCROLL_OFFSET = 150;
const NEW_MESSAGE_SEEN_THRESHOLD = 12;

interface ConversationProps {
  sourceWithItems: SourceWithItems | null;
}

const Conversation = memo(function Conversation({
  sourceWithItems,
}: ConversationProps) {
  const { t } = useTranslation("MainContent");
  const dispatch = useAppDispatch();
  const [form] = Form.useForm();
  const scrollContainerRef = useRef<HTMLDivElement>(null);
  const [messageValue, setMessageValue] = useState("");
  const [dividerItemUuid, setDividerItemUuid] = useState<string | null>(null);
  const sourceUuidRef = useRef<string | null>(null);
  const itemCountRef = useRef<number>(0);
  const dividerUuidRef = useRef<string | null>(null);
  const pendingScrollTargetRef = useRef<"divider" | "bottom" | null>(null);
  const dividerRef = useRef<HTMLDivElement | null>(null);
  const isAutoScrollingRef = useRef(false);
  const activeSourceUuid = sourceWithItems?.uuid ?? null;
  const journalistUUID = useAppSelector(
    (state) => state.session.authData?.journalistUUID ?? null,
  );
  const lastSeenInteractionCount = useAppSelector((state) =>
    activeSourceUuid
      ? selectConversationLastSeen(state, activeSourceUuid)
      : undefined,
  );

  const items = useMemo(
    () => (sourceWithItems ? sourceWithItems.items : []),
    [sourceWithItems],
  );
  const itemCount = items.length;
  const hasItems = itemCount > 0;
  const latestInteractionCount = useMemo(() => {
    return sourceWithItems?.items.at(-1)?.data.interaction_count ?? null;
  }, [sourceWithItems?.items]);

  // Load last-seen state from whatever the database already considered "seen"
  // so the divider appears immediately on cold start, before any new scroll events
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
      const interaction = item.data.interaction_count ?? null;
      if (interaction === null) {
        return false;
      }
      return interaction > threshold;
    });

    setDividerItemUuid(firstNewItem ? firstNewItem.uuid : null);
  }, [items, lastSeenInteractionCount, sourceWithItems]);

  // Track conversation transitions and detect when scroll adjustments are needed.
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

  // Jump to just above the divider so the top of the viewport lands slightly before the new items
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

  // Default behavior for initial loads or when there are no unseen items
  const scrollToBottom = useCallback(() => {
    const scrollEl = scrollContainerRef.current;
    if (!scrollEl) {
      return false;
    }
    scrollEl.scrollTop = scrollEl.scrollHeight;
    return true;
  }, []);

  const scheduleAutoScrollReset = useCallback(() => {
    const reset = () => {
      isAutoScrollingRef.current = false;
    };

    if (typeof window !== "undefined" && window.requestAnimationFrame) {
      window.requestAnimationFrame(reset);
    } else {
      setTimeout(reset, 0);
    }
  }, []);

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

  // Execute pending scroll actions once the DOM metrics are available
  useEffect(() => {
    const target = pendingScrollTargetRef.current;
    if (!target) {
      return;
    }

    if (target === "divider" && dividerItemUuid) {
      isAutoScrollingRef.current = true;
      if (scrollToDivider()) {
        pendingScrollTargetRef.current = null;
        scheduleAutoScrollReset();
      } else {
        isAutoScrollingRef.current = false;
      }
      return;
    }

    if (target === "bottom") {
      isAutoScrollingRef.current = true;
      if (scrollToBottom()) {
        pendingScrollTargetRef.current = null;
        scheduleAutoScrollReset();
      } else {
        isAutoScrollingRef.current = false;
      }
    }
  }, [
    dividerItemUuid,
    itemCount,
    scheduleAutoScrollReset,
    scrollToBottom,
    scrollToDivider,
  ]);

  // Clear the divider once the user reaches the end of the list
  useEffect(() => {
    const scrollEl = scrollContainerRef.current;
    if (!scrollEl || !dividerItemUuid) {
      return;
    }

    const handleScroll = () => {
      if (isAutoScrollingRef.current) {
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

  const designation = useMemo(
    () => sourceWithItems?.data.journalist_designation,
    [sourceWithItems?.data.journalist_designation],
  );

  const placeholderText = useMemo(
    () =>
      t("conversation.messagePlaceholder", {
        designation: designation ? toTitleCase(designation) : "",
      }),
    [t, designation],
  );

  const isSendDisabled = useMemo(
    () => !messageValue || !messageValue.trim(),
    [messageValue],
  );

  const handleSubmit = useCallback(
    async (values: { message: string }) => {
      if (!sourceWithItems || !values.message?.trim()) return;

      // Clear the form immediately for better UX
      form.resetFields();
      setMessageValue("");

      // Calculate the likely interactionCount this reply will be assigned; it
      // may not be correct (e.g. if the conversation was deleted) but it'll display
      // in the correct order while pending and then get adjusted on the server.
      const nextInteractionCount =
        (sourceWithItems.items.at(-1)?.data.interaction_count || 0) + 1;

      try {
        await window.electronAPI.addPendingReplySentEvent(
          values.message,
          sourceWithItems.uuid,
          nextInteractionCount,
        );

        // Update local state immediately with projected changes
        dispatch(fetchSources());
        dispatch(fetchConversation(sourceWithItems.uuid));
      } catch (error) {
        console.error("Failed to send reply:", error);
        // Restore the message on error
        form.setFieldsValue({ message: values.message });
        setMessageValue(values.message);
      }
    },
    [sourceWithItems, dispatch, form],
  );

  if (!sourceWithItems) return null;

  return (
    <div className="flex flex-col h-full w-full min-h-0">
      <div className="flex-1 min-h-0 relative">
        {hasItems ? (
          <div
            ref={scrollContainerRef}
            className="absolute inset-0 overflow-y-auto overflow-x-hidden p-4 pb-0"
            data-testid="conversation-items-container"
          >
            {oldItems.map((item) => (
              <Item
                key={item.uuid}
                item={item}
                designation={designation || ""}
              />
            ))}
            {newItems.length > 0 && (
              <>
                <NewMessagesDivider ref={dividerRef} />
                {newItems.map((item) => (
                  <Item
                    key={item.uuid}
                    item={item}
                    designation={designation || ""}
                  />
                ))}
              </>
            )}
          </div>
        ) : (
          <div className="flex items-center justify-center h-full">
            <EmptyConversation />
          </div>
        )}
      </div>
      <div className="flex-shrink-0 p-4 pt-0">
        <Form form={form} layout="vertical" onFinish={handleSubmit}>
          <div className="relative">
            <Form.Item name="message" style={{ marginBottom: 0 }}>
              <Input.TextArea
                data-testid="reply-textarea"
                rows={4}
                placeholder={placeholderText}
                className="w-full border border-gray-300 rounded-lg p-3 text-gray-900 resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 conversation-textarea"
                onChange={(e) => setMessageValue(e.target.value)}
              />
            </Form.Item>
            <Button
              data-testid="send-button"
              type="link"
              htmlType="submit"
              disabled={isSendDisabled}
              className="text-blue-600 hover:text-blue-800 font-medium conversation-send-btn"
            >
              {t("conversation.sendButton")}
            </Button>
          </div>
        </Form>
      </div>
    </div>
  );
});

export default Conversation;
