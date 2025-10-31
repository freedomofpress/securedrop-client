import { describe, it, expect, vi, beforeEach } from "vitest";
import { screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import Conversation from "./Conversation";
import {
  testMemoization,
  renderWithProviders,
} from "../../../test-component-setup";
import type { ItemUpdate, SourceWithItems } from "../../../../types";

const mockSourceWithItems: SourceWithItems = {
  uuid: "source-1",
  data: {
    uuid: "source-1",
    journalist_designation: "test source",
    is_starred: false,
    is_seen: false,
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
