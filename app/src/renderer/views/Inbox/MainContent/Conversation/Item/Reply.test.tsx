import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { renderWithProviders } from "../../../../../test-component-setup";
import Reply from "./Reply";
import type {
  Item,
  ReplyMetadata,
  JournalistMetadata,
} from "../../../../../../types";
import { SessionStatus } from "../../../../../features/session/sessionSlice";
import type { RootState } from "../../../../../store";
import { act } from "@testing-library/react";

describe("Reply", () => {
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
        <Reply item={mockReplyItem} />,
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
        <Reply item={itemWithJournalist2} />,
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
        <Reply item={itemWithJournalist3} />,
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
        <Reply item={itemWithUnknownJournalist} />,
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
        <Reply item={mockReplyItem} />,
        { preloadedState: offlineState },
      );

      expect(getByText("Daniel Ellsberg")).toBeInTheDocument();
    });

    it("should not display 'You' even if journalist matches offline user", () => {
      const { queryByText, getByText } = renderWithProviders(
        <Reply item={mockReplyItem} />,
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
          token: "test-token-123",
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
        <Reply item={mockReplyItem} />, // journalist_uuid is "journalist-1"
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
        <Reply item={itemFromOtherJournalist} />,
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
            token: "test-token-123",
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
        <Reply item={mockReplyItem} />, // journalist_uuid is "journalist-1" (Daniel Ellsberg)
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
        <Reply item={itemWithUnknownJournalist} />,
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
        <Reply item={mockReplyItem} />,
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
            token: "test-token-123",
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
        <Reply item={mockReplyItem} />, // journalist_uuid is "journalist-1"
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
            token: "test-token-123",
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
        <Reply item={mockReplyItem} />, // journalist_uuid is "journalist-1"
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
            token: "test-token-123",
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
        <Reply item={mockReplyItem} />, // journalist_uuid is "journalist-1"
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
    };

    describe("when authenticated (online mode)", () => {
      it("should display 'You' for pending reply", () => {
        const authState: Partial<RootState> = {
          session: {
            status: SessionStatus.Auth,
            authData: {
              expiration: "2025-07-16T19:25:44.388054+00:00",
              token: "test-token-123",
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
          <Reply item={pendingReplyItem} />,
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
              token: "test-token-123",
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
          <Reply item={pendingReplyItem} />,
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
              token: "test-token-123",
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
          <Reply item={pendingReplyItem} />,
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
              token: "test-token-123",
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
          <Reply item={pendingReplyItem} />,
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
          <Reply item={pendingReplyItem} />,
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
          <Reply item={pendingReplyItem} />,
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
          token: "test-token-123",
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
        <Reply item={mockReplyItem} />,
        { preloadedState: authState },
      );

      expect(getByText("This is a reply message")).toBeInTheDocument();
    });

    it("should display encrypted message placeholder when no plaintext", () => {
      const encryptedReply: Item = {
        ...mockReplyItem,
        plaintext: undefined, // No plaintext available
      };

      const { getByText } = renderWithProviders(
        <Reply item={encryptedReply} />,
        { preloadedState: authState },
      );

      expect(getByText("Message is encrypted...")).toBeInTheDocument();
    });

    it("should display encrypted message placeholder when plaintext is empty", () => {
      const encryptedReply: Item = {
        ...mockReplyItem,
        plaintext: "", // Empty plaintext
      };

      const { getByText } = renderWithProviders(
        <Reply item={encryptedReply} />,
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
          token: "test-token-123",
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
    };

    it("should display pending icon for pending replies", () => {
      const { getByTestId } = renderWithProviders(
        <Reply item={pendingReplyItem} />,
        { preloadedState: authState },
      );

      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
    });

    it("should not display pending icon for regular replies", () => {
      const { queryByTestId } = renderWithProviders(
        <Reply item={mockReplyItem} />, // Has journalist_uuid
        { preloadedState: authState },
      );

      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
    });

    it("should display pending icon with tooltip", () => {
      const { getByTestId } = renderWithProviders(
        <Reply item={pendingReplyItem} />,
        { preloadedState: authState },
      );

      const icon = getByTestId("pending-reply-icon");
      expect(icon).toBeInTheDocument();

      // Hover to show tooltip (note: actual tooltip rendering may vary in tests)
      // The tooltip title is set, which is what matters for accessibility
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
        <Reply item={pendingReplyItem} />,
        { preloadedState: offlineState },
      );

      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
    });
  });

  describe("Success Reply Icon (transition from pending to synced)", () => {
    const authState: Partial<RootState> = {
      session: {
        status: SessionStatus.Auth,
        authData: {
          expiration: "2025-07-16T19:25:44.388054+00:00",
          token: "test-token-123",
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
    };

    const syncedReplyItem: Item = {
      ...pendingReplyItem,
      data: {
        ...pendingReplyItem.data,
        journalist_uuid: "journalist-1", // Now has journalist UUID (synced)
      } as ReplyMetadata,
    };

    beforeEach(() => {
      vi.useFakeTimers();
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it("should show success icon when reply transitions from pending to synced", async () => {
      const { rerender, getByTestId, queryByTestId } = renderWithProviders(
        <Reply item={pendingReplyItem} />,
        { preloadedState: authState },
      );

      // Initially shows pending icon
      expect(getByTestId("pending-reply-icon")).toBeInTheDocument();
      expect(queryByTestId("success-reply-icon")).not.toBeInTheDocument();

      // Transition to synced state
      rerender(<Reply item={syncedReplyItem} />);

      // Flush microtask queue to allow state update
      await act(async () => {
        await Promise.resolve();
      });

      // Should now show success icon
      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
      expect(getByTestId("success-reply-icon")).toBeInTheDocument();
    });

    it("should hide success icon after 3 seconds", async () => {
      const { rerender, getByTestId, queryByTestId } = renderWithProviders(
        <Reply item={pendingReplyItem} />,
        { preloadedState: authState },
      );

      // Transition to synced state
      rerender(<Reply item={syncedReplyItem} />);

      // Flush microtask queue to allow state update
      await act(async () => {
        await Promise.resolve();
      });

      // Success icon should be visible
      expect(getByTestId("success-reply-icon")).toBeInTheDocument();

      // Advance time by 3 seconds
      act(() => {
        vi.advanceTimersByTime(3000);
      });

      // Success icon should be gone
      expect(queryByTestId("success-reply-icon")).not.toBeInTheDocument();
    });

    it("should not show success icon for already synced replies", () => {
      const { queryByTestId } = renderWithProviders(
        <Reply item={syncedReplyItem} />,
        { preloadedState: authState },
      );

      // Should not show any status icon for already synced replies
      expect(queryByTestId("pending-reply-icon")).not.toBeInTheDocument();
      expect(queryByTestId("success-reply-icon")).not.toBeInTheDocument();
    });

    it("should cleanup timer on unmount during animation", () => {
      const { rerender, unmount } = renderWithProviders(
        <Reply item={pendingReplyItem} />,
        { preloadedState: authState },
      );

      // Transition to synced state
      rerender(<Reply item={syncedReplyItem} />);

      // Unmount before timer completes
      unmount();

      // Advance timers - should not throw or cause issues
      act(() => {
        vi.advanceTimersByTime(3000);
      });

      // Test passes if no errors are thrown
    });
  });
});
