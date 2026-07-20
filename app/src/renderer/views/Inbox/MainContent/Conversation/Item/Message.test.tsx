import { describe, it, expect, vi, beforeEach } from "vitest";
import userEvent from "@testing-library/user-event";
import { screen, fireEvent, waitFor } from "@testing-library/react";
import Message from "./Message";
import {
  testMemoization,
  renderWithProviders,
} from "../../../../../test-component-setup";
import type {
  Item,
  ReplyMetadata,
  JournalistMetadata,
} from "../../../../../../types";
import { FetchStatus } from "../../../../../../types";
import { SessionStatus } from "../../../../../features/session/sessionSlice";
import type { RootState } from "../../../../../store";

describe("Message Component Memoization", () => {
  const mockItem: Item = {
    uuid: "item-1",
    data: {
      uuid: "item-1",
      kind: "message",
      seen_by: [],
      size: 512,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    plaintext: "Hello, this is a message",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };
  const mockOnUpdate = vi.fn();
  const mockOnDelete = vi.fn();

  const cases: Array<
    [
      {
        kind: "message";
        item: Item;
        designation: string;
        onUpdate: () => void;
        onDelete: () => void;
      },
      number,
    ]
  > = [
    // Initial render
    [
      {
        kind: "message",
        item: mockItem,
        designation: "Test Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      1,
    ],
    // Same props - should not re-render
    [
      {
        kind: "message",
        item: mockItem,
        designation: "Test Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      1,
    ],
    // Change designation - should re-render
    [
      {
        kind: "message",
        item: mockItem,
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      2,
    ],
    // Change item plaintext - should re-render
    [
      {
        kind: "message",
        item: { ...mockItem, plaintext: "Different message" },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      3,
    ],
    // Change to encrypted (no plaintext) - should re-render
    [
      {
        kind: "message",
        item: { ...mockItem, plaintext: null },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      4,
    ],
  ];

  it("should handle memoization correctly", testMemoization(Message, cases));
});

describe("Reply", () => {
  const mockOnDelete = vi.fn();

  const mockReplyItem: Item = {
    uuid: "reply-1",
    data: {
      kind: "reply",
      uuid: "reply-1",
      source: "source-1",
      size: 1024,
      journalist_uuid: "journalist-1",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: 1,
    } as ReplyMetadata,
    plaintext: "This is a reply message",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };

  const mockJournalists: Array<{ uuid: string; data: JournalistMetadata }> = [
    {
      uuid: "journalist-1",
      data: {
        uuid: "journalist-1",
        username: "dellsberg",
        first_name: "Daniel",
        last_name: "Ellsberg",
      },
    },
    {
      uuid: "journalist-2",
      data: {
        uuid: "journalist-2",
        username: "journalist",
        first_name: null,
        last_name: null,
      },
    },
    {
      uuid: "journalist-3",
      data: {
        uuid: "journalist-3",
        username: "deleted",
        first_name: "",
        last_name: "",
      },
    },
  ];

  describe("when session is unauthenticated", () => {
    const unauthState: Partial<RootState> = {
      session: {
        status: SessionStatus.Unauth,
        authData: undefined,
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    it("should display journalist full name when available", () => {
      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: unauthState },
      );

      expect(getByText("Daniel Ellsberg")).toBeInTheDocument();
    });

    it("should display username when first/last names are null", () => {
      const itemWithJournalist2: Item = {
        ...mockReplyItem,
        data: {
          ...mockReplyItem.data,
          journalist_uuid: "journalist-2",
        } as ReplyMetadata,
      };

      const { getByText } = renderWithProviders(
        <Message
          kind="reply"
          item={itemWithJournalist2}
          onDelete={mockOnDelete}
        />,
        { preloadedState: unauthState },
      );

      expect(getByText("journalist")).toBeInTheDocument();
    });

    it("should display username when first/last names are empty strings", () => {
      const itemWithJournalist3: Item = {
        ...mockReplyItem,
        data: {
          ...mockReplyItem.data,
          journalist_uuid: "journalist-3",
        } as ReplyMetadata,
      };

      const { getByText } = renderWithProviders(
        <Message
          kind="reply"
          item={itemWithJournalist3}
          onDelete={mockOnDelete}
        />,
        { preloadedState: unauthState },
      );

      expect(getByText("deleted")).toBeInTheDocument();
    });

    it("should display 'Unknown' when journalist is not found", () => {
      const itemWithUnknownJournalist: Item = {
        ...mockReplyItem,
        data: {
          ...mockReplyItem.data,
          journalist_uuid: "unknown-journalist",
        } as ReplyMetadata,
      };

      const { getByText } = renderWithProviders(
        <Message
          kind="reply"
          item={itemWithUnknownJournalist}
          onDelete={mockOnDelete}
        />,
        { preloadedState: unauthState },
      );

      expect(getByText("Unknown")).toBeInTheDocument();
    });
  });

  describe("when session is offline", () => {
    const offlineState: Partial<RootState> = {
      session: {
        status: SessionStatus.Offline,
        authData: undefined,
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    it("should display journalist name", () => {
      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: offlineState },
      );

      expect(getByText("Daniel Ellsberg")).toBeInTheDocument();
    });

    it("should not display 'You' even if journalist matches offline user", () => {
      const { queryByText, getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: offlineState },
      );

      expect(queryByText("You")).not.toBeInTheDocument();
      expect(getByText("Daniel Ellsberg")).toBeInTheDocument();
    });
  });

  describe("when session is authenticated", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-07-16T19:25:44.388054+00:00",
          journalistUUID: "journalist-1", // Current user is journalist-1
          journalistFirstName: "Daniel",
          journalistLastName: "Ellsberg",
        },
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    it("should display 'You' when current user is the author", () => {
      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // journalist_uuid is "journalist-1"
        { preloadedState: authState },
      );

      expect(getByText("You")).toBeInTheDocument();
    });

    it("should display other journalist's name when they are the author", () => {
      const itemFromOtherJournalist: Item = {
        ...mockReplyItem,
        data: {
          ...mockReplyItem.data,
          journalist_uuid: "journalist-2", // Different journalist
        } as ReplyMetadata,
      };

      const { getByText, queryByText } = renderWithProviders(
        <Message
          kind="reply"
          item={itemFromOtherJournalist}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(queryByText("You")).not.toBeInTheDocument();
      expect(getByText("journalist")).toBeInTheDocument(); // journalist-2's username
    });

    it("should display full name when other journalist has first/last names", () => {
      const authStateAsJournalist2: Partial<RootState> = {
        session: {
          status: SessionStatus.Auth,
          authData: {
            expiration: "2025-07-16T19:25:44.388054+00:00",
            journalistUUID: "journalist-2", // Current user is journalist-2
            journalistFirstName: "",
            journalistLastName: "",
          },
        },
        journalists: {
          journalists: mockJournalists,
          loading: false,
          error: null,
        },
      };

      const { getByText, queryByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // journalist_uuid is "journalist-1" (Daniel Ellsberg)
        { preloadedState: authStateAsJournalist2 },
      );

      expect(queryByText("You")).not.toBeInTheDocument();
      expect(getByText("Daniel Ellsberg")).toBeInTheDocument();
    });

    it("should display 'Unknown' when authenticated and journalist not found", () => {
      const itemWithUnknownJournalist: Item = {
        ...mockReplyItem,
        data: {
          ...mockReplyItem.data,
          journalist_uuid: "unknown-journalist",
        } as ReplyMetadata,
      };

      const { getByText, queryByText } = renderWithProviders(
        <Message
          kind="reply"
          item={itemWithUnknownJournalist}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(queryByText("You")).not.toBeInTheDocument();
      expect(getByText("Unknown")).toBeInTheDocument();
    });
  });

  describe("edge cases", () => {
    it("should handle empty journalists list when unauthenticated", () => {
      const emptyJournalistsState: Partial<RootState> = {
        session: {
          status: SessionStatus.Unauth,
          authData: undefined,
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: emptyJournalistsState },
      );

      expect(getByText("Unknown")).toBeInTheDocument();
    });

    it("should display 'You' when authenticated even if journalists list is empty (current user)", () => {
      const emptyJournalistsAuthState: Partial<RootState> = {
        session: {
          status: SessionStatus.Auth,
          authData: {
            expiration: "2025-07-16T19:25:44.388054+00:00",
            journalistUUID: "journalist-1", // Same as the reply author
            journalistFirstName: "Daniel",
            journalistLastName: "Ellsberg",
          },
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // journalist_uuid is "journalist-1"
        { preloadedState: emptyJournalistsAuthState },
      );

      expect(getByText("You")).toBeInTheDocument();
    });

    it("should display 'You' when journalists still loading (current user)", () => {
      const loadingState: Partial<RootState> = {
        session: {
          status: SessionStatus.Auth,
          authData: {
            expiration: "2025-07-16T19:25:44.388054+00:00",
            journalistUUID: "journalist-1", // Same as reply author
            journalistFirstName: "Daniel",
            journalistLastName: "Ellsberg",
          },
        },
        journalists: {
          journalists: [],
          loading: true,
          error: null,
        },
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // journalist_uuid is "journalist-1"
        { preloadedState: loadingState },
      );

      expect(getByText("You")).toBeInTheDocument();
    });

    it("should display 'Unknown' when authenticated but different journalist not in empty list", () => {
      const emptyJournalistsAuthState: Partial<RootState> = {
        session: {
          status: SessionStatus.Auth,
          authData: {
            expiration: "2025-07-16T19:25:44.388054+00:00",
            journalistUUID: "journalist-2", // Different from reply author
            journalistFirstName: "Current",
            journalistLastName: "User",
          },
        },
        journalists: {
          journalists: [],
          loading: false,
          error: null,
        },
      };

      const { getByText, queryByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // journalist_uuid is "journalist-1"
        { preloadedState: emptyJournalistsAuthState },
      );

      expect(queryByText("You")).not.toBeInTheDocument();
      expect(getByText("Unknown")).toBeInTheDocument();
    });
  });

  describe("pending replies (empty journalist_uuid)", () => {
    const pendingReplyItem: Item = {
      uuid: "pending-reply-1",
      data: {
        kind: "reply",
        uuid: "pending-reply-1",
        source: "source-1",
        size: 1024,
        journalist_uuid: "", // Empty UUID indicates pending reply
        is_deleted_by_source: false,
        seen_by: [],
        interaction_count: 1,
      } as ReplyMetadata,
      plaintext: "This is a pending reply",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    describe("when authenticated (online mode)", () => {
      it("should display 'You' for pending reply", () => {
        const authState: Partial<RootState> = {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-07-16T19:25:44.388054+00:00",
              journalistUUID: "journalist-1",
              journalistFirstName: "Daniel",
              journalistLastName: "Ellsberg",
            },
          },
          journalists: {
            journalists: mockJournalists,
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: authState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });

      it("should display 'You' even when not in journalists list", () => {
        const authState: Partial<RootState> = {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-07-16T19:25:44.388054+00:00",
              journalistUUID: "journalist-99", // Not in journalists list
              journalistFirstName: "New",
              journalistLastName: "User",
            },
          },
          journalists: {
            journalists: mockJournalists,
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: authState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });

      it("should display 'You' when current user has no first/last name", () => {
        const authState: Partial<RootState> = {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-07-16T19:25:44.388054+00:00",
              journalistUUID: "journalist-2", // This journalist has no first/last name
              journalistFirstName: "",
              journalistLastName: "",
            },
          },
          journalists: {
            journalists: [], // Empty list
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: authState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });

      it("should display 'You' even when only first name is provided", () => {
        const authState: Partial<RootState> = {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-07-16T19:25:44.388054+00:00",
              journalistUUID: "journalist-99",
              journalistFirstName: "John",
              journalistLastName: "",
            },
          },
          journalists: {
            journalists: [],
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: authState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });
    });

    describe("when offline", () => {
      it("should display 'You' for pending reply", () => {
        const offlineState: Partial<RootState> = {
          session: {
            status: SessionStatus.Offline,
            authData: undefined,
          },
          journalists: {
            journalists: mockJournalists,
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: offlineState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });
    });

    describe("when unauthenticated (edge case)", () => {
      it("should display 'You' for pending reply", () => {
        const unauthState: Partial<RootState> = {
          session: {
            status: SessionStatus.Unauth,
            authData: undefined,
          },
          journalists: {
            journalists: mockJournalists,
            loading: false,
            error: null,
          },
        };

        const { getByText } = renderWithProviders(
          <Message
            kind="reply"
            item={pendingReplyItem}
            onDelete={mockOnDelete}
          />,
          { preloadedState: unauthState },
        );

        expect(getByText("You")).toBeInTheDocument();
      });
    });
  });

  describe("message content", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-07-16T19:25:44.388054+00:00",
          journalistUUID: "journalist-1",
          journalistFirstName: "Daniel",
          journalistLastName: "Ellsberg",
        },
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    it("should display plaintext message when available", () => {
      const { getByText } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("This is a reply message")).toBeInTheDocument();
    });

    it("shows fetching placeholder when fetch_status is Initial", () => {
      const fetchingReply: Item = {
        ...mockReplyItem,
        plaintext: null, // No plaintext available
        fetch_status: FetchStatus.Initial,
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={fetchingReply} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("Fetching message...")).toBeInTheDocument();
    });

    it("shows fetching placeholder when fetch_status is DownloadInProgress", () => {
      const fetchingReply: Item = {
        ...mockReplyItem,
        plaintext: null,
        fetch_status: FetchStatus.DownloadInProgress,
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={fetchingReply} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("Fetching message...")).toBeInTheDocument();
    });

    it("shows encrypted placeholder when fetch_status is DecryptionInProgress", () => {
      const decryptingReply: Item = {
        ...mockReplyItem,
        plaintext: null,
        fetch_status: FetchStatus.DecryptionInProgress,
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={decryptingReply} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("Message is encrypted...")).toBeInTheDocument();
    });

    it("shows download failed error with retry when fetch_status is FailedDownloadRetryable", () => {
      const failedDownloadReply: Item = {
        ...mockReplyItem,
        plaintext: null,
        fetch_status: FetchStatus.FailedDownloadRetryable,
      };

      const { getByText } = renderWithProviders(
        <Message
          kind="reply"
          item={failedDownloadReply}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(getByText("Failed to download message")).toBeInTheDocument();
    });

    it("shows decryption failed error with retry when fetch_status is FailedDecryptionRetryable", () => {
      const failedDecryptionReply: Item = {
        ...mockReplyItem,
        plaintext: null,
        fetch_status: FetchStatus.FailedDecryptionRetryable,
      };

      const { getByText } = renderWithProviders(
        <Message
          kind="reply"
          item={failedDecryptionReply}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(getByText("Failed to decrypt message")).toBeInTheDocument();
    });

    it("should display encrypted message placeholder when no plaintext and no fetch status", () => {
      const encryptedReply: Item = {
        ...mockReplyItem,
        plaintext: null,
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={encryptedReply} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("Message is encrypted...")).toBeInTheDocument();
    });

    it("should display encrypted message placeholder when plaintext is empty", () => {
      const encryptedReply: Item = {
        ...mockReplyItem,
        plaintext: "",
      };

      const { getByText } = renderWithProviders(
        <Message kind="reply" item={encryptedReply} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByText("Message is encrypted...")).toBeInTheDocument();
    });
  });

  describe("Pending Reply Icon", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-07-16T19:25:44.388054+00:00",
          journalistUUID: "journalist-1",
          journalistFirstName: "Daniel",
          journalistLastName: "Ellsberg",
        },
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    const pendingReplyItem: Item = {
      uuid: "pending-reply-1",
      data: {
        kind: "reply",
        uuid: "pending-reply-1",
        source: "source-1",
        size: 1024,
        journalist_uuid: "", // Empty UUID indicates pending reply
        is_deleted_by_source: false,
        seen_by: [],
        // FIXME
        interaction_count: 0,
      } as ReplyMetadata,
      plaintext: "This is a pending reply",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    it("should display pending icon for pending replies", () => {
      const { getByTestId } = renderWithProviders(
        <Message
          kind="reply"
          item={pendingReplyItem}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
    });

    it("should not display pending icon for regular replies", () => {
      const { queryByTestId } = renderWithProviders(
        <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />, // Has journalist_uuid
        { preloadedState: authState },
      );

      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
    });

    it("should display pending icon with tooltip", () => {
      const { getByTestId } = renderWithProviders(
        <Message
          kind="reply"
          item={pendingReplyItem}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      const icon = getByTestId("pending-reply-icon");
      expect(icon).toBeInTheDocument();

      const tooltipContainer = icon.parentElement;
      expect(tooltipContainer).toBeInTheDocument();
    });

    it("should display pending icon when offline", () => {
      const offlineState: Partial<RootState> = {
        session: {
          status: SessionStatus.Offline,
          authData: undefined,
        },
        journalists: {
          journalists: mockJournalists,
          loading: false,
          error: null,
        },
      };

      const { getByTestId } = renderWithProviders(
        <Message
          kind="reply"
          item={pendingReplyItem}
          onDelete={mockOnDelete}
        />,
        { preloadedState: offlineState },
      );

      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
    });
  });

  describe("Persistent status icons", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-07-16T19:25:44.388054+00:00",
          journalistUUID: "journalist-1",
          journalistFirstName: "Daniel",
          journalistLastName: "Ellsberg",
        },
      },
      journalists: {
        journalists: mockJournalists,
        loading: false,
        error: null,
      },
    };

    const pendingReplyItem: Item = {
      uuid: "pending-reply-1",
      data: {
        kind: "reply",
        uuid: "pending-reply-1",
        source: "source-1",
        size: 1024,
        journalist_uuid: "", // Empty UUID indicates pending reply
        is_deleted_by_source: false,
        seen_by: [],
        interaction_count: 1,
      } as ReplyMetadata,
      plaintext: "This is a pending reply",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    const sentReplyItem: Item = {
      uuid: "sent-reply-1",
      data: {
        kind: "reply",
        uuid: "sent-reply-1",
        source: "source-1",
        size: 1024,
        journalist_uuid: "journalist-1",
        is_deleted_by_source: false,
        seen_by: [],
        interaction_count: 1,
      } as ReplyMetadata,
      plaintext: "This is a sent reply",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    const seenReplyItem: Item = {
      uuid: "seen-reply-1",
      data: {
        kind: "reply",
        uuid: "seen-reply-1",
        source: "source-1",
        size: 1024,
        journalist_uuid: "journalist-1",
        is_deleted_by_source: true, // Source has seen and deleted it
        seen_by: [],
        interaction_count: 1,
      } as ReplyMetadata,
      plaintext: "This is a seen reply",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    it("should show pending icon for pending replies", () => {
      const { getByTestId, queryByTestId } = renderWithProviders(
        <Message
          kind="reply"
          item={pendingReplyItem}
          onDelete={mockOnDelete}
        />,
        { preloadedState: authState },
      );

      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
      expect(queryByTestId("sent-reply-icon")).not.toBeInTheDocument();
      expect(queryByTestId("seen-reply-icon")).not.toBeInTheDocument();
    });

    it("should show sent icon for synced replies not yet seen by source", () => {
      const { getByTestId, queryByTestId } = renderWithProviders(
        <Message kind="reply" item={sentReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByTestId("sent-reply-icon")).toBeInTheDocument();
      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
      expect(queryByTestId("seen-reply-icon")).not.toBeInTheDocument();
    });

    it("should show seen icon when source has seen the reply", () => {
      const { getByTestId, queryByTestId } = renderWithProviders(
        <Message kind="reply" item={seenReplyItem} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByTestId("seen-reply-icon")).toBeInTheDocument();
      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
      expect(queryByTestId("sent-reply-icon")).not.toBeInTheDocument();
    });

    it("should show sent icon when is_deleted_by_source is false", () => {
      const notDeletedItem: Item = {
        ...sentReplyItem,
        data: {
          ...(sentReplyItem.data as ReplyMetadata),
          is_deleted_by_source: false,
        } as ReplyMetadata,
      };

      const { getByTestId, queryByTestId } = renderWithProviders(
        <Message kind="reply" item={notDeletedItem} onDelete={mockOnDelete} />,
        { preloadedState: authState },
      );

      expect(getByTestId("sent-reply-icon")).toBeInTheDocument();
      expect(queryByTestId("seen-reply-icon")).not.toBeInTheDocument();
    });
  });
});

describe("Message and Reply delete button keyboard accessibility", () => {
  const mockOnDelete = vi.fn();

  const authState: Partial<import("../../../../../store").RootState> = {
    session: {
      status: SessionStatus.Auth,
      authData: {
        expiration: "2025-07-16T19:25:44.388054+00:00",
        journalistUUID: "journalist-1",
        journalistFirstName: "Daniel",
        journalistLastName: "Ellsberg",
      },
    },
    journalists: { journalists: [], loading: false, error: null },
  };

  const mockMessageItem: Item = {
    uuid: "msg-1",
    data: {
      uuid: "msg-1",
      kind: "message",
      seen_by: [],
      size: 512,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    plaintext: "Hello",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };

  const mockReplyItem: Item = {
    uuid: "reply-1",
    data: {
      kind: "reply",
      uuid: "reply-1",
      source: "source-1",
      size: 1024,
      journalist_uuid: "journalist-1",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: 1,
    } as import("../../../../../../types").ReplyMetadata,
    plaintext: "A reply",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it("message delete button has an accessible label", () => {
    renderWithProviders(
      <Message
        kind="message"
        item={mockMessageItem}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={mockOnDelete}
      />,
      { preloadedState: authState },
    );

    expect(
      screen.getByRole("button", { name: "Delete message" }),
    ).toBeInTheDocument();
  });

  it("reply delete button has an accessible label", () => {
    renderWithProviders(
      <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
      { preloadedState: authState },
    );

    expect(
      screen.getByRole("button", { name: "Delete reply" }),
    ).toBeInTheDocument();
  });

  it("message delete button is reachable by keyboard and becomes visible on focus", async () => {
    renderWithProviders(
      <Message
        kind="message"
        item={mockMessageItem}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={mockOnDelete}
      />,
      { preloadedState: authState },
    );

    const deleteBtn = screen.getByRole("button", { name: "Delete message" });
    const wrapper = deleteBtn.closest(".transition-opacity") as HTMLElement;

    // Starts hidden
    expect(wrapper.style.opacity).toBe("0");

    fireEvent.focus(deleteBtn);
    expect(wrapper.style.opacity).toBe("1");
  });

  it("reply delete button is reachable by keyboard and becomes visible on focus", () => {
    renderWithProviders(
      <Message kind="reply" item={mockReplyItem} onDelete={mockOnDelete} />,
      { preloadedState: authState },
    );

    const deleteBtn = screen.getByRole("button", { name: "Delete reply" });
    const wrapper = deleteBtn.closest(".transition-opacity") as HTMLElement;

    expect(wrapper.style.opacity).toBe("0");

    fireEvent.focus(deleteBtn);
    expect(wrapper.style.opacity).toBe("1");
  });

  it("message delete button calls onDelete when activated by keyboard", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <Message
        kind="message"
        item={mockMessageItem}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={mockOnDelete}
      />,
      { preloadedState: authState },
    );

    const deleteBtn = screen.getByRole("button", { name: "Delete message" });
    deleteBtn.focus();
    await user.keyboard("{Enter}");

    expect(mockOnDelete).toHaveBeenCalledOnce();
  });
});

describe("Double-encryption badge", () => {
  const authState: Partial<RootState> = {
    session: {
      status: SessionStatus.Auth,
      authData: {
        expiration: "2025-07-16T19:25:44.388054+00:00",
        journalistUUID: "journalist-1",
        journalistFirstName: "Daniel",
        journalistLastName: "Ellsberg",
      },
    },
    journalists: { journalists: [], loading: false, error: null },
  };

  const mockMessageItem: Item = {
    uuid: "msg-1",
    data: {
      uuid: "msg-1",
      kind: "message",
      seen_by: [],
      size: 512,
      source: "source-1",
      is_read: false,
      interaction_count: 0,
    },
    plaintext: "A pre-encrypted message",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };

  const mockReplyItem: Item = {
    uuid: "reply-1",
    data: {
      kind: "reply",
      uuid: "reply-1",
      source: "source-1",
      size: 1024,
      journalist_uuid: "journalist-1",
      is_deleted_by_source: false,
      seen_by: [],
      interaction_count: 1,
    } as ReplyMetadata,
    plaintext: "A reply",
    filename: null,
    fetch_status: null,
    fetch_progress: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };

  it("shows the normal badge when the inner layer used the current submission key", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <Message
        kind="message"
        item={{
          ...mockMessageItem,
          doubleEncryptedKeyFingerprint:
            "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
        }}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    const badge = screen.getByText("Source-encrypted");
    expect(badge).toBeInTheDocument();
    await waitFor(() =>
      expect(window.electronAPI.getSubmissionKeyFingerprint).toHaveBeenCalled(),
    );
    expect(badge.style.color).toBe("");
    await user.hover(badge);
    expect(
      await screen.findByText(
        "This submission was encrypted by the source before uploading",
      ),
    ).toBeInTheDocument();
    expect(
      (await screen.findByRole("tooltip")).closest(".ant-tooltip"),
    ).toHaveClass("ant-tooltip-placement-bottom");
    // The message itself is still displayed
    expect(screen.getByText("A pre-encrypted message")).toBeInTheDocument();
  });

  it("normalizes case and spacing when comparing full fingerprints", async () => {
    vi.mocked(window.electronAPI.getSubmissionKeyFingerprint).mockResolvedValue(
      "aaaa aaaa aaaa aaaa aaaa aaaa aaaa aaaa aaaa aaaa",
    );
    renderWithProviders(
      <Message
        kind="message"
        item={{
          ...mockMessageItem,
          doubleEncryptedKeyFingerprint:
            "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
        }}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    const badge = screen.getByText("Source-encrypted");
    await waitFor(() =>
      expect(window.electronAPI.getSubmissionKeyFingerprint).toHaveBeenCalled(),
    );
    expect(badge.style.color).toBe("");
  });

  it("does not treat a matching 16-character key ID as the current key", async () => {
    renderWithProviders(
      <Message
        kind="message"
        item={{
          ...mockMessageItem,
          doubleEncryptedKeyFingerprint: "AAAAAAAAAAAAAAAA",
        }}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    const badge = screen.getByText("Source-encrypted");
    await waitFor(() => expect(badge.style.color).not.toBe(""));
  });

  it("shows a warning badge with the fingerprint in the tooltip when the inner layer used a non-submission key", async () => {
    const user = userEvent.setup();
    const { container } = renderWithProviders(
      <Message
        kind="message"
        item={{
          ...mockMessageItem,
          doubleEncryptedKeyFingerprint:
            "1234567890ABCDEF1234567890ABCDEF12345678",
        }}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    const badge = screen.getByText("Source-encrypted");
    expect(badge).toBeInTheDocument();
    // Same padlock icon, but tinted with the warning color
    expect(container.querySelector(".lucide-lock-keyhole")).toBeTruthy();
    await waitFor(() => expect(badge.style.color).not.toBe(""));

    // The tooltip names the key's fingerprint, formatted in 4-char groups
    await user.hover(badge);
    expect(
      await screen.findByText(
        /1234 5678 90AB CDEF 1234 5678 90AB CDEF 1234 5678/,
      ),
    ).toBeInTheDocument();
  });

  it("does not show the badge on a normal message", () => {
    renderWithProviders(
      <Message
        kind="message"
        item={mockMessageItem}
        designation="Test Source"
        onUpdate={vi.fn()}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    expect(screen.queryByText("Source-encrypted")).not.toBeInTheDocument();
  });

  it("does not show the badge on a reply, even if flagged", () => {
    // Replies are authored by journalists and are never source-double-encrypted
    renderWithProviders(
      <Message
        kind="reply"
        item={{
          ...mockReplyItem,
          doubleEncryptedKeyFingerprint:
            "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
        }}
        onDelete={vi.fn()}
      />,
      { preloadedState: authState },
    );

    expect(screen.queryByText("Source-encrypted")).not.toBeInTheDocument();
  });
});
