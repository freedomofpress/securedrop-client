import { describe, it, vi } from "vitest";
import React from "react";
import Conversation from "./Conversation";
import { renderAndCheckA11y } from "../../../test-component-setup";
import type { SourceWithItems } from "../../../../types";

// Stub out Element.prototype.scrollTo so the conversation scroll logic doesn't
// error in jsdom, which doesn't implement it.
Element.prototype.scrollTo = vi.fn(function (
  this: Element,
  optionsOrX?: ScrollToOptions | number,
) {
  if (
    typeof optionsOrX === "object" &&
    optionsOrX !== null &&
    "top" in optionsOrX &&
    optionsOrX.top !== undefined
  ) {
    (this as HTMLElement).scrollTop = optionsOrX.top;
  }
}) as unknown as typeof Element.prototype.scrollTo;

// Mirror the react-window mock from Conversation.test.tsx so the virtual list
// renders rows and the useConversationScroll hooks (useDynamicRowHeight,
// useListCallbackRef) are provided without DOM measurement.
vi.mock("react-window", () => {
  return {
    List: ({
      rowComponent: RowComponent,
      rowCount,
      rowProps,
      listRef,
    }: {
      rowComponent: (props: {
        index: number;
        style: React.CSSProperties;
        [k: string]: unknown;
      }) => React.ReactNode;
      rowCount: number;
      rowHeight: unknown;
      rowProps: Record<string, unknown>;
      listRef?: (api: unknown) => void;
      [k: string]: unknown;
    }) => {
      const containerRef = React.useRef<HTMLDivElement>(null);
      React.useEffect(() => {
        if (listRef && containerRef.current) {
          const el = containerRef.current;
          listRef({
            get element() {
              return el;
            },
            scrollToRow({ index, align }: { index?: number; align?: string }) {
              if (el) {
                if (align === "end") {
                  el.scrollTop = el.scrollHeight;
                } else if (align === "center" && index !== undefined) {
                  const rowEl = el.children[index] as HTMLElement | undefined;
                  if (rowEl) {
                    el.scrollTop = Math.max(
                      0,
                      rowEl.offsetTop - el.clientHeight / 2,
                    );
                  }
                }
              }
            },
          });
        }
      }, [listRef]);
      return (
        <div ref={containerRef} data-testid="conversation-items-container">
          {Array.from({ length: rowCount }, (_, i) => (
            <div key={i}>
              <RowComponent index={i} style={{}} {...rowProps} />
            </div>
          ))}
        </div>
      );
    },
    useDynamicRowHeight: () =>
      React.useMemo(
        () => ({
          getAverageRowHeight: () => 400,
          getRowHeight: () => 400,
          setRowHeight: () => {},
          observeRowElements: () => () => {},
        }),
        [],
      ),
    useListCallbackRef: () => React.useState<null>(null),
  };
});

// ---------------------------------------------------------------------------
// Shared fixture data
// ---------------------------------------------------------------------------

const makeSource = (items: SourceWithItems["items"] = []): SourceWithItems => ({
  uuid: "source-1",
  data: {
    uuid: "source-1",
    journalist_designation: "test source",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    last_updated: "2025-01-15T10:00:00Z",
    public_key: "test-public-key",
    fingerprint: "test-fingerprint",
  },
  items,
});

const messageItem = (
  uuid: string,
  interactionCount: number,
): SourceWithItems["items"][number] => ({
  uuid,
  data: {
    kind: "message",
    uuid,
    source: "source-1",
    size: 1024,
    seen_by: [],
    is_read: false,
    interaction_count: interactionCount,
  },
  plaintext: "Hello from a source",
  filename: null,
  decrypted_size: null,
  fetch_progress: 1024,
  fetch_status: 3,
});

const replyItem = (
  uuid: string,
  interactionCount: number,
): SourceWithItems["items"][number] => ({
  uuid,
  data: {
    kind: "reply",
    uuid,
    source: "source-1",
    size: 512,
    journalist_uuid: "journalist-1",
    seen_by: [],
    is_deleted_by_source: false,
    interaction_count: interactionCount,
  },
  plaintext: "Reply from journalist",
  filename: null,
  decrypted_size: null,
  fetch_progress: 512,
  fetch_status: 3,
});

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe("Conversation accessibility", () => {
  it("has no axe violations when no source is selected (renders nothing)", async () => {
    // When sourceWithItems is null the component returns null — nothing to
    // scan, but the wrapper container itself should still be clean.
    await renderAndCheckA11y(<Conversation sourceWithItems={null} />);
  });

  it("has no axe violations on an empty conversation (no items yet)", async () => {
    await renderAndCheckA11y(<Conversation sourceWithItems={makeSource([])} />);
  });

  it("has no axe violations with messages and replies loaded", async () => {
    await renderAndCheckA11y(
      <Conversation
        sourceWithItems={makeSource([
          messageItem("item-1", 1),
          replyItem("reply-1", 2),
          messageItem("item-2", 3),
        ])}
      />,
    );
  });

  it("has no axe violations with a pre-populated reply draft", async () => {
    await renderAndCheckA11y(
      <Conversation sourceWithItems={makeSource([messageItem("item-1", 1)])} />,
      {
        preloadedState: {
          drafts: {
            drafts: { "source-1": "draft reply text" },
          },
        },
      },
    );
  });
});
