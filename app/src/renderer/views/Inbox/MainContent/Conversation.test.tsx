import { describe, it, expect, vi, beforeEach } from "vitest";
import { act, screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import Conversation from "./Conversation";
import {
  testMemoization,
  renderWithProviders,
} from "../../../test-component-setup";
import { SessionStatus } from "../../../features/session/sessionSlice";
import type { ItemUpdate, SourceWithItems } from "../../../../types";

const mockSourceWithItems: SourceWithItems = {
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
  items: [
    {
      uuid: "item-1",
      data: {
        kind: "message",
        uuid: "item-1",
        source: "source-1",
        size: 1024,
        seen_by: [],
        is_read: false,
        interaction_count: 1,
      },
      fetch_progress: 1024,
      fetch_status: 3,
    },
  ],
};

const createMessageItem = (
  uuid: string,
  interactionCount: number,
  options?: { seenBy?: string[]; isRead?: boolean },
): SourceWithItems["items"][number] => ({
  uuid,
  data: {
    kind: "message",
    uuid,
    source: "source-1",
    size: 1024,
    seen_by: options?.seenBy ?? [],
    is_read: options?.isRead ?? false,
    interaction_count: interactionCount,
  },
  fetch_progress: 1024,
  fetch_status: 3,
});

const createReplyItem = (
  uuid: string,
  interactionCount: number,
): SourceWithItems["items"][number] => ({
  uuid,
  data: {
    kind: "reply",
    uuid,
    source: "source-1",
    size: 1024,
    journalist_uuid: "journalist-1",
    seen_by: [],
    is_deleted_by_source: false,
    interaction_count: interactionCount,
  },
  fetch_progress: 1024,
  fetch_status: 3,
});

const withItems = (items: SourceWithItems["items"]): SourceWithItems => ({
  ...mockSourceWithItems,
  data: { ...mockSourceWithItems.data },
  items,
});

describe("Conversation Component Memoization", () => {
  const mockOnUpdate: (_: ItemUpdate) => void = vi.fn();

  const cases: Array<
    [
      {
        sourceWithItems: SourceWithItems | null;
        onItemUpdate: (_: ItemUpdate) => void;
      },
      number,
    ]
  > = [
    // Initial render with source
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 1],
    // Same props - should not re-render
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 1],
    // Null source - should re-render
    [{ sourceWithItems: null, onItemUpdate: mockOnUpdate }, 2],
    // Back to same source - should re-render
    [{ sourceWithItems: mockSourceWithItems, onItemUpdate: mockOnUpdate }, 3],
    // Different source - should re-render
    [
      {
        sourceWithItems: {
          ...mockSourceWithItems,
          uuid: "source-2",
          data: { ...mockSourceWithItems.data, uuid: "source-2" },
        },
        onItemUpdate: mockOnUpdate,
      },
      4,
    ],
  ];

  it(
    "should handle memoization correctly",
    testMemoization(Conversation, cases),
  );
});

describe("Conversation Component Reply Submission", () => {
  let mockAddPendingReplySentEvent: ReturnType<typeof vi.fn>;

  beforeEach(() => {
    mockAddPendingReplySentEvent = vi.fn().mockResolvedValue(BigInt(123));
    window.electronAPI = {
      ...window.electronAPI,
      addPendingReplySentEvent: mockAddPendingReplySentEvent,
    };
  });

  it("should submit reply when form is submitted with valid message", async () => {
    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    // Type a message
    await userEvent.type(textarea, "This is my reply");

    // Verify the textarea has the typed value
    expect(textarea).toHaveValue("This is my reply");

    // Submit the form
    await userEvent.click(sendButton);

    // Verify IPC was called with correct arguments
    await waitFor(() => {
      expect(mockAddPendingReplySentEvent).toHaveBeenCalledWith(
        "This is my reply",
        "source-1",
        2,
      );
    });

    // Note: Form clearing is handled by form.resetFields() but may not reflect
    // immediately in the test DOM. The important part is that the IPC was called.
  });

  it("should not submit reply when message is empty", async () => {
    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const sendButton = screen.getByTestId("send-button");

    // Button should be disabled when empty
    expect(sendButton).toBeDisabled();

    // Try to submit without typing anything
    await userEvent.click(sendButton);

    // Verify IPC was not called
    expect(mockAddPendingReplySentEvent).not.toHaveBeenCalled();
  });

  it("should not submit reply when message contains only whitespace", async () => {
    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    // Type only whitespace
    await userEvent.type(textarea, "   ");

    // Button should be disabled when only whitespace
    expect(sendButton).toBeDisabled();

    // Try to submit
    await userEvent.click(sendButton);

    // Verify IPC was not called
    expect(mockAddPendingReplySentEvent).not.toHaveBeenCalled();
  });

  it("should handle submission errors gracefully", async () => {
    const consoleErrorSpy = vi
      .spyOn(console, "error")
      .mockImplementation(() => {});
    mockAddPendingReplySentEvent.mockRejectedValue(new Error("Network error"));

    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    // Type a message
    await userEvent.type(textarea, "This is my reply");

    // Submit the form
    await userEvent.click(sendButton);

    // Verify error was logged
    await waitFor(() => {
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        "Failed to send reply:",
        expect.any(Error),
      );
    });

    // Verify the form was restored with the original message since submission failed
    await waitFor(() => {
      expect(textarea).toHaveValue("This is my reply");
    });

    consoleErrorSpy.mockRestore();
  });

  it("should submit reply with multiline text", async () => {
    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    // Type a multiline message
    const multilineMessage = "Line 1\nLine 2\nLine 3";
    await userEvent.type(textarea, multilineMessage);

    // Submit the form
    await userEvent.click(sendButton);

    // Verify IPC was called with the multiline message
    await waitFor(() => {
      expect(mockAddPendingReplySentEvent).toHaveBeenCalledWith(
        multilineMessage,
        "source-1",
        2,
      );
    });

    // Note: Form clearing is handled by form.resetFields() but may not reflect
    // immediately in the test DOM. The important part is that the IPC was called.
  });

  it("should enable send button only when message has non-whitespace content", async () => {
    renderWithProviders(<Conversation sourceWithItems={mockSourceWithItems} />);

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    // Initially disabled
    expect(sendButton).toBeDisabled();

    // Type some text - button should be enabled
    await userEvent.type(textarea, "Hello");
    expect(sendButton).toBeEnabled();

    // Clear the text - button should be disabled again
    await userEvent.clear(textarea);
    expect(sendButton).toBeDisabled();

    // Type whitespace only - button should remain disabled
    await userEvent.type(textarea, "   ");
    expect(sendButton).toBeDisabled();

    // Add actual content - button should be enabled
    await userEvent.type(textarea, "Real message");
    expect(sendButton).toBeEnabled();
  });
});

describe("Conversation new message indicator", () => {
  const baseItems = [createMessageItem("item-1", 1)];

  it("restores indicator from previously seen history", async () => {
    const source = withItems([
      createMessageItem("item-1", 1, {
        seenBy: ["journalist-1"],
        isRead: true,
      }),
      createMessageItem("item-2", 2, {
        seenBy: ["journalist-1"],
        isRead: true,
      }),
      createMessageItem("item-3", 3),
    ]);

    const { store } = renderWithProviders(
      <Conversation sourceWithItems={source} />,
      {
        preloadedState: {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-01-01T00:00:00Z",
              token: "token",
              journalistUUID: "journalist-1",
              journalistFirstName: "Test",
              journalistLastName: "User",
            },
          },
        },
      },
    );

    await waitFor(() => {
      expect(
        store.getState().sources.conversationIndicators["source-1"],
      ).toEqual({ lastSeenInteractionCount: 2 });
    });

    expect(
      await screen.findByTestId("new-messages-divider"),
    ).toBeInTheDocument();
  });

  it("renders divider when new items arrive and scrolls near them", async () => {
    const { rerender } = renderWithProviders(
      <Conversation sourceWithItems={withItems(baseItems)} />,
    );

    expect(
      screen.queryByTestId("new-messages-divider"),
    ).not.toBeInTheDocument();

    const container = screen.getByTestId(
      "conversation-items-container",
    ) as HTMLDivElement;

    let scrollTopValue = 0;
    Object.defineProperty(container, "scrollHeight", {
      configurable: true,
      value: 1000,
    });
    Object.defineProperty(container, "clientHeight", {
      configurable: true,
      value: 400,
    });
    Object.defineProperty(container, "scrollTop", {
      configurable: true,
      get: () => scrollTopValue,
      set: (value) => {
        scrollTopValue = value;
      },
    });

    const offsetSpy = vi
      .spyOn(HTMLElement.prototype, "offsetTop", "get")
      .mockReturnValue(400);

    rerender(
      <Conversation
        sourceWithItems={withItems([
          ...baseItems,
          createMessageItem("item-2", 2),
          createMessageItem("item-3", 3),
        ])}
      />,
    );

    await screen.findByTestId("new-messages-divider");

    await waitFor(() => {
      expect(scrollTopValue).toBe(250);
    });

    const renderedItems = screen.getAllByTestId(/item-/);
    expect(renderedItems).toHaveLength(3);

    offsetSpy.mockRestore();
  });

  it("does not render divider for new replies", async () => {
    const { rerender } = renderWithProviders(
      <Conversation sourceWithItems={withItems(baseItems)} />,
    );

    rerender(
      <Conversation
        sourceWithItems={withItems([
          ...baseItems,
          createReplyItem("reply-1", 2),
        ])}
      />,
    );

    await waitFor(() => {
      expect(
        screen.queryByTestId("new-messages-divider"),
      ).not.toBeInTheDocument();
    });
  });

  it("clears divider immediately after sending reply", async () => {
    const { rerender } = renderWithProviders(
      <Conversation sourceWithItems={withItems(baseItems)} />,
    );

    rerender(
      <Conversation
        sourceWithItems={withItems([
          ...baseItems,
          createMessageItem("item-2", 2),
        ])}
      />,
    );

    await screen.findByTestId("new-messages-divider");

    const textarea = screen.getByTestId("reply-textarea");
    const sendButton = screen.getByTestId("send-button");

    await userEvent.type(textarea, "reply message");
    await userEvent.click(sendButton);

    await waitFor(() => {
      expect(
        screen.queryByTestId("new-messages-divider"),
      ).not.toBeInTheDocument();
    });
  });

  it("clears divider once user scrolls to the bottom", async () => {
    const { rerender } = renderWithProviders(
      <Conversation sourceWithItems={withItems(baseItems)} />,
    );

    const container = screen.getByTestId(
      "conversation-items-container",
    ) as HTMLDivElement;

    Object.defineProperty(container, "scrollHeight", {
      configurable: true,
      value: 1200,
    });
    Object.defineProperty(container, "clientHeight", {
      configurable: true,
      value: 500,
    });
    let scrollTopValue = 0;
    Object.defineProperty(container, "scrollTop", {
      configurable: true,
      get: () => scrollTopValue,
      set: (value) => {
        scrollTopValue = value;
      },
    });

    const originalRAF = window.requestAnimationFrame;
    const rafCallbacks: FrameRequestCallback[] = [];
    (window as any).requestAnimationFrame = vi.fn(
      (cb: FrameRequestCallback) => {
        rafCallbacks.push(cb);
        return 0;
      },
    ) as typeof window.requestAnimationFrame;

    rerender(
      <Conversation
        sourceWithItems={withItems([
          ...baseItems,
          createMessageItem("item-2", 2),
        ])}
      />,
    );

    await screen.findByTestId("new-messages-divider");

    await act(async () => {
      rafCallbacks.forEach((cb) => cb(0));
    });
    if (originalRAF) {
      window.requestAnimationFrame = originalRAF;
    } else {
      delete (window as any).requestAnimationFrame;
    }

    await act(async () => {
      container.scrollTop = container.scrollHeight;
      container.dispatchEvent(new Event("scroll"));
    });

    await waitFor(() => {
      expect(
        screen.queryByTestId("new-messages-divider"),
      ).not.toBeInTheDocument();
    });
  });

  it("keeps divider visible while auto-scrolling", async () => {
    const { rerender } = renderWithProviders(
      <Conversation sourceWithItems={withItems(baseItems)} />,
    );

    const container = screen.getByTestId(
      "conversation-items-container",
    ) as HTMLDivElement;

    Object.defineProperty(container, "scrollHeight", {
      configurable: true,
      value: 1000,
    });
    Object.defineProperty(container, "clientHeight", {
      configurable: true,
      value: 400,
    });
    let scrollTopValue = 0;
    Object.defineProperty(container, "scrollTop", {
      configurable: true,
      get: () => scrollTopValue,
      set: (value) => {
        scrollTopValue = value;
      },
    });

    const offsetSpy = vi
      .spyOn(HTMLElement.prototype, "offsetTop", "get")
      .mockReturnValue(400);

    const originalRAF = window.requestAnimationFrame;
    const rafCallbacks: FrameRequestCallback[] = [];
    (window as any).requestAnimationFrame = vi.fn(
      (cb: FrameRequestCallback) => {
        rafCallbacks.push(cb);
        return 0;
      },
    ) as typeof window.requestAnimationFrame;

    rerender(
      <Conversation
        sourceWithItems={withItems([
          ...baseItems,
          createMessageItem("item-2", 2),
        ])}
      />,
    );

    await screen.findByTestId("new-messages-divider");

    await waitFor(() => {
      expect(scrollTopValue).toBe(250);
    });

    container.dispatchEvent(new Event("scroll"));

    expect(screen.getByTestId("new-messages-divider")).toBeInTheDocument();

    await act(async () => {
      rafCallbacks.forEach((cb) => cb(0));
    });
    if (originalRAF) {
      window.requestAnimationFrame = originalRAF;
    } else {
      delete (window as any).requestAnimationFrame;
    }
    offsetSpy.mockRestore();
  });
});
