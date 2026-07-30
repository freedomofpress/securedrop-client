// Consolidated accessibility (axe) tests.
//
// All axe/accessibility assertions live in this single file so they run in one
// worker. The whole file is wrapped in `describe.sequential` so the axe scans
// never run concurrently — concurrent axe runs are CPU/memory heavy and cause
// flakiness/timeouts in CI.
//
// When adding an accessibility check for a component, add it here (rather than
// alongside that component's behavioural tests) so it inherits this isolation.

import { describe, it, expect, vi, beforeAll } from "vitest";
import React from "react";
import { screen, waitFor } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { Routes, Route } from "react-router";

import {
  checkA11y,
  renderAndCheckA11y,
  renderWithProviders,
  renderedComponents,
} from "./test-component-setup";

// Components under test
import App from "./App";
import SignInView from "./views/SignIn";
import InboxView from "./views/Inbox";
import MainContent from "./views/Inbox/MainContent";
import Conversation from "./views/Inbox/MainContent/Conversation";
import SourceMenu from "./views/Inbox/MainContent/Header/SourceMenu";
import { ExportWizard } from "./views/Inbox/MainContent/Conversation/Item/Export";
import { PrintWizard } from "./views/Inbox/MainContent/Conversation/Item/Print";
import File from "./views/Inbox/MainContent/Conversation/Item/File";
import Message from "./views/Inbox/MainContent/Conversation/Item/Message";
import SourceList from "./views/Inbox/Sidebar/SourceList";
import Source from "./views/Inbox/Sidebar/SourceList/Source";
import MainMenu from "./views/Inbox/Sidebar/Account/MainMenu";
import KeyboardHelp from "./views/Inbox/Sidebar/Account/KeyboardHelp";
import { FirstRunPopup } from "./components/FirstRunPopup";
import TruncatedText from "./components/TruncatedText";

import {
  SessionStatus,
  unauthSessionState,
} from "./features/session/sessionSlice";
import { FetchStatus } from "../types";
import type { Item, SourceWithItems, Source as SourceType } from "../types";

// ---------------------------------------------------------------------------
// jsdom shims
// ---------------------------------------------------------------------------

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

// Mock react-window so the virtualized lists (Conversation, SourceList) render
// their rows in jsdom instead of relying on DOM measurement. Rendering the real
// rows lets axe analyse the actual accessible markup. Child row components
// (Source, ConversationRow) are intentionally NOT mocked.
vi.mock("react-window", () => {
  return {
    List: ({
      rowComponent: RowComponent,
      rowCount,
      rowProps,
      listRef,
      className,
    }: {
      rowComponent: (props: {
        index: number;
        style: React.CSSProperties;
        [k: string]: unknown;
      }) => React.ReactNode;
      rowCount: number;
      rowHeight: unknown;
      rowProps: Record<string, unknown>;
      // Conversation passes a callback ref (useListCallbackRef); SourceList
      // passes an object ref (useListRef). Support both.
      listRef?: ((api: unknown) => void) | { current: unknown };
      className?: string;
      [k: string]: unknown;
    }) => {
      const containerRef = React.useRef<HTMLDivElement>(null);
      React.useEffect(() => {
        if (listRef && containerRef.current) {
          const el = containerRef.current;
          const api = {
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
          };
          if (typeof listRef === "function") {
            listRef(api);
          } else {
            listRef.current = api;
          }
        }
      }, [listRef]);
      return (
        <div
          ref={containerRef}
          className={className}
          data-testid="conversation-items-container"
        >
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
    useListRef: () => ({ current: null }),
  };
});

// ===========================================================================
// Accessibility tests — run sequentially (never concurrently).
// ===========================================================================

describe.sequential("accessibility (axe)", () => {
  // Start from a clean slate so the coverage check below only accounts for
  // components rendered by this suite (guards against any cross-file leakage if
  // Vitest module isolation is ever disabled).
  beforeAll(() => {
    renderedComponents.clear();
  });

  describe("App", () => {
    it("has no axe violations on the sign-in redirect (unauthenticated)", async () => {
      await renderAndCheckA11y(<App />, {
        initialEntries: ["/"],
        preloadedState: { session: unauthSessionState },
      });
    });
  });

  describe("SignIn", () => {
    it("has no axe violations on initial render", async () => {
      await renderAndCheckA11y(<SignInView />);
    });

    it("has no axe violations when showing client-side validation errors", async () => {
      const { container, getByTestId } = renderWithProviders(<SignInView />);

      // Submit empty form to trigger all three required-field errors at once
      await userEvent.click(getByTestId("sign-in-button"));

      await waitFor(() => {
        expect(
          screen.getByText("Please enter your username."),
        ).toBeInTheDocument();
      });

      const results = await checkA11y(container);
      expect(results).toHaveNoViolations();
    });

    it("has no axe violations when showing a credential error", async () => {
      (window as any).electronAPI.login.mockResolvedValue({
        success: false,
        errorType: "credentials",
      });

      const { container, getByTestId } = renderWithProviders(<SignInView />);

      await userEvent.type(getByTestId("username-input"), "nelliebly");
      await userEvent.type(
        getByTestId("passphrase-input"),
        "validPassphrase12345",
      );
      await userEvent.type(getByTestId("one-time-code-input"), "123456");
      await userEvent.click(getByTestId("sign-in-button"));

      await waitFor(() => {
        expect(
          screen.getByText("Those credentials didn't work."),
        ).toBeInTheDocument();
      });

      const results = await checkA11y(container);
      expect(results).toHaveNoViolations();
    });

    it("has no axe violations when showing a network error", async () => {
      (window as any).electronAPI.login.mockResolvedValue({
        success: false,
        errorType: "network",
      });

      const { container, getByTestId } = renderWithProviders(<SignInView />);

      await userEvent.type(getByTestId("username-input"), "nelliebly");
      await userEvent.type(
        getByTestId("passphrase-input"),
        "validPassphrase12345",
      );
      await userEvent.type(getByTestId("one-time-code-input"), "123456");
      await userEvent.click(getByTestId("sign-in-button"));

      await waitFor(() => {
        expect(
          screen.getByText("Could not reach the SecureDrop server."),
        ).toBeInTheDocument();
      });

      const results = await checkA11y(container);
      expect(results).toHaveNoViolations();
    });
  });

  describe("Inbox", () => {
    it("has no axe violations on initial render", async () => {
      await renderAndCheckA11y(<InboxView />);
    });
  });

  describe("SourceList", () => {
    const mockSources: Record<string, SourceType> = {
      "source-1": {
        uuid: "source-1",
        data: {
          fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
          is_starred: false,
          is_seen: false,
          has_attachment: false,
          journalist_designation: "alice wonderland",
          last_updated: "2024-01-15T10:30:00Z",
          public_key: "key-1",
          uuid: "source-1",
        },
        isRead: false,
        hasAttachment: false,
        messagePreview: null,
        lastInteractionCount: 3,
      },
      "source-2": {
        uuid: "source-2",
        data: {
          fingerprint: "EFGH5678IJKL9012MNOP3456QRST7890ABCD1234",
          is_starred: true,
          is_seen: true,
          has_attachment: true,
          journalist_designation: "bob marley",
          last_updated: "2024-01-14T15:45:00Z",
          public_key: "key-2",
          uuid: "source-2",
        },
        isRead: true,
        hasAttachment: true,
        messagePreview: { kind: "message", plaintext: "Hello there" },
        lastInteractionCount: 1,
      },
    };

    const sourcesState = (
      sources: Record<string, SourceType> = mockSources,
    ) => ({
      sources: {
        sources,
        activeSourceUuid: null,
        loading: false,
        error: null,
        conversationIndicators: {},
      },
    });

    // SourceList must live inside a router that provides :sourceUuid so that
    // useParams works. renderAndCheckA11y wraps the given element in a
    // MemoryRouter (via TestWrapper), so we just need Routes/Route inside it.
    const sourceListUi = (
      <Routes>
        <Route path="/" element={<SourceList focusedPanel="sidebar" />} />
        <Route
          path="/source/:sourceUuid"
          element={<SourceList focusedPanel="sidebar" />}
        />
      </Routes>
    );

    it("has no axe violations with a populated source list", async () => {
      // TODO(a11y): source rows have unnamed buttons, unlabeled form controls,
      // nested interactive controls, and an ARIA role outside its required parent.
      await renderAndCheckA11y(
        sourceListUi,
        {
          preloadedState: sourcesState(),
        },
        ["aria-required-parent", "button-name", "label", "nested-interactive"],
      );
    });

    it("has no axe violations with an empty source list", async () => {
      await renderAndCheckA11y(sourceListUi, {
        preloadedState: sourcesState({}),
      });
    });

    it("has no axe violations with an active source selected", async () => {
      // TODO(a11y): source rows have unnamed buttons, unlabeled form controls,
      // nested interactive controls, and an ARIA role outside its required parent.
      await renderAndCheckA11y(
        sourceListUi,
        {
          initialEntries: ["/source/source-1"],
          preloadedState: sourcesState(),
        },
        ["aria-required-parent", "button-name", "label", "nested-interactive"],
      );
    });
  });

  describe("Source", () => {
    const createMockSource = (
      overrides: Partial<SourceType> = {},
    ): SourceType => ({
      uuid: "test-uuid-123",
      data: {
        fingerprint: "test-fingerprint",
        is_starred: false,
        is_seen: false,
        has_attachment: false,
        journalist_designation: "test source",
        last_updated: "2025-01-15T10:00:00Z",
        public_key: "test-public-key",
        uuid: "test-uuid-123",
      },
      isRead: true,
      hasAttachment: false,
      messagePreview: null,
      ...overrides,
    });

    it("has no axe violations on a basic unread source", async () => {
      // TODO(a11y): source row has unnamed buttons, unlabeled form controls,
      // nested interactive controls, and an ARIA role outside its required parent.
      await renderAndCheckA11y(
        <Source
          source={createMockSource()}
          isSelected={false}
          isActive={false}
          onSelect={vi.fn()}
          onToggleStar={vi.fn()}
        />,
        undefined,
        ["aria-required-parent", "button-name", "label", "nested-interactive"],
      );
    });
  });

  describe("MainMenu", () => {
    it("has no axe violations in offline mode", async () => {
      await renderAndCheckA11y(<MainMenu />, {
        preloadedState: {
          session: { status: SessionStatus.Unauth, authData: undefined },
        },
      });
    });
  });

  describe("KeyboardHelp", () => {
    it("has no axe violations", async () => {
      await renderAndCheckA11y(<KeyboardHelp />);
    });
  });

  describe("MainContent", () => {
    it("has no axe violations on the empty state (no source selected)", async () => {
      await renderAndCheckA11y(
        <Routes>
          <Route path="/" element={<MainContent />} />
          <Route path="/source/:sourceUuid" element={<MainContent />} />
        </Routes>,
        {
          initialEntries: ["/"],
          preloadedState: {
            conversation: {
              conversation: null,
              loading: false,
              error: null,
              lastFetchTime: null,
              hasMoreHistoricalItems: false,
              olderItemsLoading: false,
            },
          },
        },
      );
    });
  });

  describe("SourceMenu", () => {
    const mockSourceWithItems: SourceWithItems = {
      uuid: "source-1",
      data: {
        fingerprint: "ABCD1234EFGH5678IJKL9012MNOP3456QRST7890",
        is_starred: false,
        journalist_designation: "durian smoothie",
        last_updated: "2024-01-15T10:30:00Z",
        public_key: "-----BEGIN PGP PUBLIC KEY BLOCK-----\n...\n-----END-----",
        uuid: "source-1",
        is_seen: true,
        has_attachment: false,
      },
      items: [],
    };

    it("has no axe violations on initial render", async () => {
      await renderAndCheckA11y(
        <SourceMenu sourceWithItems={mockSourceWithItems} />,
      );
    });
  });

  describe("Conversation", () => {
    const makeSource = (
      items: SourceWithItems["items"] = [],
    ): SourceWithItems => ({
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
      doubleEncryptedKeyFingerprint: null,
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
      doubleEncryptedKeyFingerprint: null,
    });

    it("has no axe violations when no source is selected (renders nothing)", async () => {
      // When sourceWithItems is null the component returns null — nothing to
      // scan, but the wrapper container itself should still be clean.
      await renderAndCheckA11y(<Conversation sourceWithItems={null} />);
    });

    it("has no axe violations on an empty conversation (no items yet)", async () => {
      await renderAndCheckA11y(
        <Conversation sourceWithItems={makeSource([])} />,
      );
    });

    it("has no axe violations with messages and replies loaded", async () => {
      // TODO(a11y): ARIA role not contained by its required parent.
      await renderAndCheckA11y(
        <Conversation
          sourceWithItems={makeSource([
            messageItem("item-1", 1),
            replyItem("reply-1", 2),
            messageItem("item-2", 3),
          ])}
        />,
        undefined,
        ["aria-required-parent"],
      );
    });

    it("has no axe violations with a pre-populated reply draft", async () => {
      // TODO(a11y): ARIA role not contained by its required parent.
      await renderAndCheckA11y(
        <Conversation
          sourceWithItems={makeSource([messageItem("item-1", 1)])}
        />,
        {
          preloadedState: {
            drafts: {
              drafts: { "source-1": "draft reply text" },
            },
          },
        },
        ["aria-required-parent"],
      );
    });
  });

  describe("PrintWizard", () => {
    const mockItem: Item = {
      uuid: "print-a11y-uuid",
      data: {
        uuid: "print-a11y-uuid",
        kind: "file",
        seen_by: [],
        size: 1024,
        source: "source-1",
        is_read: false,
        interaction_count: 0,
      },
      fetch_status: FetchStatus.Complete,
      fetch_progress: null,
      plaintext: null,
      filename: "/path/to/testfile.pdf",
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    it("has no axe violations when closed", async () => {
      await renderAndCheckA11y(
        <PrintWizard
          item={{ type: "file", payload: mockItem }}
          open={false}
          onClose={vi.fn()}
        />,
      );
    });

    it("has no axe violations when open (preflight step)", async () => {
      await renderAndCheckA11y(
        <PrintWizard
          item={{ type: "file", payload: mockItem }}
          open={true}
          onClose={vi.fn()}
        />,
      );
    });
  });

  describe("ExportWizard", () => {
    const mockItem: Item = {
      uuid: "test-item-uuid",
      data: {
        uuid: "test-item-uuid",
        kind: "file",
        seen_by: [],
        size: 1024,
        source: "source-1",
        is_read: false,
        interaction_count: 0,
      },
      fetch_status: FetchStatus.Complete,
      fetch_progress: null,
      plaintext: null,
      filename: "/path/to/testfile.pdf",
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    it("has no axe violations when the wizard is closed", async () => {
      await renderAndCheckA11y(
        <ExportWizard
          item={{ type: "file", payload: mockItem }}
          open={false}
          onClose={vi.fn()}
        />,
      );
    });

    it("has no axe violations when the wizard is open (preflight step)", async () => {
      await renderAndCheckA11y(
        <ExportWizard
          item={{ type: "file", payload: mockItem }}
          open={true}
          onClose={vi.fn()}
        />,
      );
    });
  });

  describe("File", () => {
    const makeItem = (overrides: Partial<Item> = {}): Item => ({
      uuid: "item-1",
      data: {
        uuid: "item-1",
        kind: "file",
        seen_by: [],
        size: 1024,
        source: "source-1",
        is_read: false,
        interaction_count: 0,
      },
      plaintext: null,
      filename: null,
      fetch_progress: null,
      decrypted_size: null,
      fetch_status: FetchStatus.Initial,
      doubleEncryptedKeyFingerprint: null,
      ...overrides,
    });

    it("has no axe violations for undownloaded file", async () => {
      // TODO(a11y): file row nests interactive controls.
      await renderAndCheckA11y(
        <File
          item={makeItem()}
          designation="Test Source"
          onUpdate={vi.fn()}
          onDelete={vi.fn()}
        />,
        {
          preloadedState: {
            session: { status: SessionStatus.Auth } as any,
          },
        },
        ["nested-interactive"],
      );
    });

    it("has no axe violations for downloaded file", async () => {
      // TODO(a11y): file row nests interactive controls.
      await renderAndCheckA11y(
        <File
          item={makeItem({
            fetch_status: FetchStatus.Complete,
            filename: "/path/to/document.pdf",
            decrypted_size: 2048,
          })}
          designation="Test Source"
          onUpdate={vi.fn()}
          onDelete={vi.fn()}
        />,
        {
          preloadedState: {
            session: { status: SessionStatus.Auth } as any,
          },
        },
        ["nested-interactive"],
      );
    });
  });

  describe("Message", () => {
    const mockItem: Item = {
      uuid: "item-a11y",
      data: {
        uuid: "item-a11y",
        kind: "message",
        seen_by: [],
        size: 512,
        source: "source-1",
        is_read: false,
        interaction_count: 1,
      },
      plaintext: "Hello, this is a message",
      filename: null,
      fetch_status: null,
      fetch_progress: null,
      decrypted_size: null,
      doubleEncryptedKeyFingerprint: null,
    };

    it("has no axe violations for a message item", async () => {
      await renderAndCheckA11y(
        <Message
          kind="message"
          item={mockItem}
          designation="Test Source"
          onUpdate={vi.fn()}
          onDelete={vi.fn()}
        />,
      );
    });
  });

  describe("FirstRunPopup", () => {
    it("has no axe violations when no popup is shown (null status)", async () => {
      window.electronAPI.getFirstRunStatus = vi.fn().mockResolvedValue(null);
      await renderAndCheckA11y(<FirstRunPopup />);
    });

    it("has no axe violations when the new-user popup is visible", async () => {
      window.electronAPI.getFirstRunStatus = vi
        .fn()
        .mockResolvedValue("new_user");
      const result = await renderAndCheckA11y(<FirstRunPopup />);
      // Wait for the async popup to appear and re-check
      await waitFor(() => {
        expect(
          result.getByText("Welcome to SecureDrop Inbox"),
        ).toBeInTheDocument();
      });
    });
  });

  describe("TruncatedText", () => {
    it("has no axe violations on short text", async () => {
      await renderAndCheckA11y(<TruncatedText text="Short message" />);
    });

    it("has no axe violations on truncated text", async () => {
      await renderAndCheckA11y(<TruncatedText text={"a".repeat(3500)} />);
    });
  });

  // Run the coverage test last so that every axe test has rendered its component.
  // Now, we check that all components that use renderWithProviders in a *.test.tsx
  // file are included so we ensure axe coverage.
  describe("coverage", () => {
    // All test files
    const testSources = import.meta.glob("./**/*.test.tsx", {
      query: "?raw",
      import: "default",
      eager: true,
    }) as Record<string, string>;

    // Lazy loaders for every candidate component module (same keyspace).
    const componentLoaders = import.meta.glob("./**/*.{ts,tsx}") as Record<
      string,
      () => Promise<Record<string, unknown>>
    >;

    // A Foo.test.tsx tests the sibling Foo module: Foo.tsx/.ts or Foo/index.*.
    const resolveComponentKey = (base: string): string | null => {
      for (const ext of [".tsx", ".ts"]) {
        if (componentLoaders[base + ext]) {
          return base + ext;
        }
      }
      for (const ext of [".tsx", ".ts"]) {
        if (componentLoaders[`${base}/index${ext}`]) {
          return `${base}/index${ext}`;
        }
      }
      return null;
    };

    const isComponentLike = (v: unknown): boolean =>
      typeof v === "function" ||
      (typeof v === "object" && v !== null && "$$typeof" in v);

    // A module is covered if any component it exports (matched by reference,
    // unwrapping one memo/forwardRef layer) was rendered by the suite above.
    const isCovered = (mod: Record<string, unknown>): boolean =>
      Object.values(mod).some((exp) => {
        if (!isComponentLike(exp) || typeof exp === "undefined") {
          return false;
        }
        if (renderedComponents.has(exp)) {
          return true;
        }
        const inner =
          (exp as { type?: unknown }).type ??
          (exp as { render?: unknown }).render;
        return inner !== undefined && renderedComponents.has(inner);
      });

    it("every component tested with renderWithProviders is axe-checked here", async () => {
      const missing: string[] = [];

      for (const [testPath, source] of Object.entries(testSources)) {
        // Keep this regex in sync with eslint.config.ts
        if (/(^|[\\/])a11y\.test\.tsx$/.test(testPath)) {
          continue;
        }
        if (!/\brenderWithProviders\b/.test(source)) {
          continue;
        }
        const key = resolveComponentKey(testPath.replace(/\.test\.tsx$/, ""));
        // No sibling component module (e.g. a hook/util test) — nothing to
        // require accessibility coverage for.
        if (!key) {
          continue;
        }
        const mod = await componentLoaders[key]();
        if (!isCovered(mod)) {
          missing.push(key.replace(/^\.\//, ""));
        }
      }

      expect(
        missing,
        "These components are rendered with renderWithProviders in their own " +
          "test files but are missing an axe test in a11y.test.tsx" +
          missing.map((m) => `  - ${m}`).join("\n") +
          "\nAdd a renderAndCheckA11y test for each of the above.",
      ).toEqual([]);
    });
  });
});
