import { screen, fireEvent } from "@testing-library/react";
import { expect, describe, it, vi } from "vitest";
import userEvent from "@testing-library/user-event";
import File from "./File";
import {
  renderWithProviders,
  testMemoization,
} from "../../../../../test-component-setup";
import {
  FetchStatus,
  ItemUpdateType,
  type Item,
} from "../../../../../../types";
import { SessionStatus } from "../../../../../features/session/sessionSlice";

describe("File Component Memoization", () => {
  const mockOnUpdate = vi.fn();
  const mockOnDelete = vi.fn();
  const mockItem: Item = {
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
    isDoubleEncrypted: false,
    fetch_status: FetchStatus.Initial,
  };

  const cases: Array<
    [
      {
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
        item: mockItem,
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      2,
    ],
    // Change item - should re-render
    [
      {
        item: { ...mockItem, uuid: "item-2" },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      3,
    ],
    // Change fetch_status - should re-render
    [
      {
        item: {
          ...mockItem,
          uuid: "item-2",
          fetch_status: FetchStatus.Complete,
        },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      4,
    ],
    [
      {
        item: {
          ...mockItem,
          uuid: "item-2",
          fetch_status: FetchStatus.ScheduledDeletion,
        },
        designation: "Different Source",
        onUpdate: mockOnUpdate,
        onDelete: mockOnDelete,
      },
      5,
    ],
  ];

  it("should handle memoization correctly", testMemoization(File, cases));
});

describe("File Component", () => {
  const mockOnUpdate = vi.fn();
  const mockOnDelete = vi.fn();

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
    isDoubleEncrypted: false,
    fetch_status: FetchStatus.Initial,
    ...overrides,
  });

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it("download button has an accessible label", () => {
    renderWithProviders(
      <File
        item={makeItem()}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    const downloadButton = screen.getByRole("button", {
      name: "Download file",
    });
    expect(downloadButton).toBeInTheDocument();
  });

  it("download button triggers onUpdate when activated by keyboard", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <File
        item={makeItem()}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    const downloadButton = screen.getByRole("button", {
      name: "Download file",
    });
    downloadButton.focus();
    await user.keyboard("{Enter}");

    expect(mockOnUpdate).toHaveBeenCalledWith({
      item_uuid: "item-1",
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  });

  it("download button is disabled and not triggerable in offline mode", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <File
        item={makeItem()}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Offline } as any,
        },
      },
    );

    const downloadButton = screen.getByRole("button", {
      name: "Download file",
    });
    expect(downloadButton).toBeDisabled();

    await user.click(downloadButton);
    expect(mockOnUpdate).not.toHaveBeenCalled();
  });

  it("'Delete item' in dropdown is keyboard-accessible", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: false,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    const actionsButton = screen.getByRole("button", { name: "File actions" });
    actionsButton.focus();
    await user.keyboard("{Enter}");

    const deleteItem = await screen.findByRole("menuitem", {
      name: "Delete item",
    });
    expect(deleteItem).toBeInTheDocument();
  });

  it("'Delete item' does not appear in file actions dropdown in offline mode", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: false,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Offline } as any,
        },
      },
    );

    // In offline mode the "File actions" button is still rendered (View/Export/Print
    // remain available), but the destructive "Delete item" must not appear in the menu.
    const actionsButton = screen.getByRole("button", { name: "File actions" });
    await user.click(actionsButton);

    expect(
      screen.queryByRole("menuitem", { name: "Delete item" }),
    ).not.toBeInTheDocument();
  });

  it("download button click does not dispatch action twice (no double-dispatch)", async () => {
    const user = userEvent.setup();
    renderWithProviders(
      <File
        item={makeItem()}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    const downloadButton = screen.getByRole("button", {
      name: "Download file",
    });
    await user.click(downloadButton);

    // The action should be dispatched exactly once even though the button is
    // inside a fileBox div that also has an onClick handler.
    expect(mockOnUpdate).toHaveBeenCalledOnce();
  });

  it("encrypted file info area is keyboard-focusable so tooltip is reachable", () => {
    const { container } = renderWithProviders(
      <File
        item={makeItem()}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    // Check that tabIndex=0 is properly set so keyboard users can focus the tooltip
    const tooltipTrigger = container.querySelector(
      ".w-80.file-box[tabindex='0']",
    );
    expect(tooltipTrigger).not.toBeNull();
    expect(tooltipTrigger).toHaveAttribute("tabindex", "0");
  });

  it("hover-reveal trash button is always in the tab order", () => {
    const { container } = renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: false,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    // The trash button starts hidden (opacity 0) when not hovered, but it must
    // remain in the tab order so keyboard users can reach and trigger it.
    const trashButton = container.querySelector(
      "[data-testid='file-delete-button']",
    );
    expect(trashButton).not.toBeNull();
    // check that it has a discoverable tabindex (not -1)
    expect(trashButton).not.toHaveAttribute("tabindex", "-1");
  });

  it("hover-reveal trash button becomes visible when focused", () => {
    const { container } = renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: false,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    const trashButton = container.querySelector(
      "[data-testid='file-delete-button']",
    ) as HTMLElement;
    expect(trashButton).not.toBeNull();

    // Before focus the wrapper is opacity 0
    const wrapper = trashButton.closest(".transition-opacity") as HTMLElement;
    expect(wrapper.style.opacity).toBe("0");

    // fireEvent.focus triggers the React onFocus handler and flushes state,
    // which should make the button visible so keyboard users can see it.
    fireEvent.focus(trashButton);
    expect(wrapper.style.opacity).toBe("1");
  });

  it("shows the double-encryption badge on a downloaded double-encrypted file", () => {
    renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: true,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    expect(screen.getByText("Source-encrypted")).toBeInTheDocument();
  });

  it("does not show the double-encryption badge on a normal file", () => {
    renderWithProviders(
      <File
        item={makeItem({
          fetch_status: FetchStatus.Complete,
          filename: "/path/to/document.pdf",
          decrypted_size: 2048,
          isDoubleEncrypted: false,
        })}
        designation="Test Source"
        onUpdate={mockOnUpdate}
        onDelete={mockOnDelete}
      />,
      {
        preloadedState: {
          session: { status: SessionStatus.Auth } as any,
        },
      },
    );

    expect(screen.queryByText("Source-encrypted")).not.toBeInTheDocument();
  });
});
