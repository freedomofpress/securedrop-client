import { screen } from "@testing-library/react";
import { expect, describe, it, vi } from "vitest";
import userEvent from "@testing-library/user-event";
import {
  renderWithProviders,
  testMemoization,
} from "../../../../test-component-setup";
import Source from "./Source";
import type { Source as SourceType } from "../../../../../types";

// Mock useNavigate
const mockNavigate = vi.fn();
vi.mock("react-router", async (importOriginal) => {
  const actual = await importOriginal<typeof import("react-router")>();
  return {
    ...actual,
    useNavigate: () => mockNavigate,
  };
});

// Mock functions for props
const mockOnSelect = vi.fn();
const mockOnToggleStar = vi.fn();
const mockOnCancelPendingStar = vi.fn();

// Helper function to create a mock source
const createMockSource = (overrides: Partial<SourceType> = {}): SourceType => ({
  uuid: "test-uuid-123",
  data: {
    fingerprint: "test-fingerprint",
    is_starred: false,
    journalist_designation: "test source",
    last_updated: "2025-01-15T10:00:00Z",
    public_key: "test-public-key",
    uuid: "test-uuid-123",
  },
  isRead: true,
  hasAttachment: false,
  showMessagePreview: false,
  messagePreview: "",
  ...overrides,
});

// Default props
const defaultProps = {
  isSelected: false,
  isActive: false,
  onSelect: mockOnSelect,
  onToggleStar: mockOnToggleStar,
  onCancelPendingStar: mockOnCancelPendingStar,
};

describe("Source Component", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockNavigate.mockClear();
  });

  describe("isRead functionality", () => {
    it("displays designation with bold font when source is unread", () => {
      const unreadSource = createMockSource({ isRead: false });
      renderWithProviders(<Source source={unreadSource} {...defaultProps} />);

      const designation = screen.getByTestId(
        "source-designation-test-uuid-123",
      );
      expect(designation.className).toContain("font-bold");
      expect(designation.className).not.toContain("font-medium");
    });

    it("displays designation with medium font when source is read", () => {
      const readSource = createMockSource({ isRead: true });
      renderWithProviders(<Source source={readSource} {...defaultProps} />);

      const designation = screen.getByTestId(
        "source-designation-test-uuid-123",
      );
      expect(designation.className).toContain("font-medium");
      expect(designation.className).not.toContain("font-bold");
    });
  });

  describe("hasAttachment functionality", () => {
    it("displays attachment icon when source has attachment", () => {
      const sourceWithAttachment = createMockSource({ hasAttachment: true });
      renderWithProviders(
        <Source source={sourceWithAttachment} {...defaultProps} />,
      );

      const attachmentIcon = screen.getByTestId("attachment-icon");
      expect(attachmentIcon).toBeDefined();
    });

    it("does not display attachment icon when source has no attachment", () => {
      const sourceWithoutAttachment = createMockSource({
        hasAttachment: false,
      });
      renderWithProviders(
        <Source source={sourceWithoutAttachment} {...defaultProps} />,
      );

      const attachmentIcon = screen.queryByTestId("attachment-icon");
      expect(attachmentIcon).toBeNull();
    });
  });

  describe("message preview functionality", () => {
    it("does not display message preview when showMessagePreview is false", () => {
      const sourceWithoutPreview = createMockSource({
        showMessagePreview: false,
        messagePreview: "This should not be shown",
      });
      renderWithProviders(
        <Source source={sourceWithoutPreview} {...defaultProps} />,
      );

      const messagePreview = screen.queryByTestId("message-preview");
      expect(messagePreview).toBeNull();
    });

    it("displays 'encrypted...' when showMessagePreview is true but messagePreview is empty", () => {
      const sourceWithEmptyPreview = createMockSource({
        showMessagePreview: true,
        messagePreview: "",
      });
      renderWithProviders(
        <Source source={sourceWithEmptyPreview} {...defaultProps} />,
      );

      const messagePreview = screen.getByTestId("message-preview");
      expect(messagePreview).toBeDefined();
      expect(messagePreview.textContent).toBe("encrypted...");
    });

    it("displays actual message preview when showMessagePreview is true and messagePreview has content", () => {
      const testMessage = "This is a test message preview";
      const sourceWithPreview = createMockSource({
        showMessagePreview: true,
        messagePreview: testMessage,
      });
      renderWithProviders(
        <Source source={sourceWithPreview} {...defaultProps} />,
      );

      const messagePreview = screen.getByTestId("message-preview");
      expect(messagePreview).toBeDefined();
      expect(messagePreview.textContent).toBe(testMessage);
    });
  });

  describe("checkbox selection functionality", () => {
    it("displays checked checkbox when isSelected is true", () => {
      const source = createMockSource();
      renderWithProviders(
        <Source source={source} {...defaultProps} isSelected={true} />,
      );

      const checkbox = screen.getByTestId(
        "source-checkbox-test-uuid-123",
      ) as HTMLInputElement;
      expect(checkbox.checked).toBe(true);
    });

    it("displays unchecked checkbox when isSelected is false", () => {
      const source = createMockSource();
      renderWithProviders(
        <Source source={source} {...defaultProps} isSelected={false} />,
      );

      const checkbox = screen.getByTestId(
        "source-checkbox-test-uuid-123",
      ) as HTMLInputElement;
      expect(checkbox.checked).toBe(false);
    });

    it("calls onSelect when checkbox is clicked", async () => {
      const user = userEvent.setup();
      const source = createMockSource();
      renderWithProviders(
        <Source source={source} {...defaultProps} isSelected={false} />,
      );

      const checkbox = screen.getByTestId("source-checkbox-test-uuid-123");
      await user.click(checkbox);

      expect(mockOnSelect).toHaveBeenCalledWith("test-uuid-123", true);
    });
  });

  describe("active state styling", () => {
    it("applies active styling when isActive is true", () => {
      const source = createMockSource();
      const { container } = renderWithProviders(
        <Source source={source} {...defaultProps} isActive={true} />,
      );

      const sourceElement = container.firstChild as HTMLElement;
      expect(sourceElement.className).toContain("bg-blue-500");
      expect(sourceElement.className).toContain("text-white");
    });

    it("does not apply active styling when isActive is false", () => {
      const source = createMockSource();
      const { container } = renderWithProviders(
        <Source source={source} {...defaultProps} isActive={false} />,
      );

      const sourceElement = container.firstChild as HTMLElement;
      expect(sourceElement.className).not.toContain("bg-blue-500");
      expect(sourceElement.className).not.toContain("text-white");
    });
  });

  describe("interaction handlers", () => {
    it("navigates to source when clicked and not active", async () => {
      const user = userEvent.setup();
      const source = createMockSource();
      const { container } = renderWithProviders(
        <Source source={source} {...defaultProps} isActive={false} />,
      );

      const sourceElement = container.firstChild as HTMLElement;
      await user.click(sourceElement);

      expect(mockNavigate).toHaveBeenCalledWith("/source/test-uuid-123");
    });

    it("navigates to home when clicked and already active", async () => {
      const user = userEvent.setup();
      const source = createMockSource();
      const { container } = renderWithProviders(
        <Source source={source} {...defaultProps} isActive={true} />,
      );

      const sourceElement = container.firstChild as HTMLElement;
      await user.click(sourceElement);

      expect(mockNavigate).toHaveBeenCalledWith("/");
    });

    it("calls onToggleStar when star button is clicked", async () => {
      const user = userEvent.setup();
      const starredSource = createMockSource({
        data: {
          ...createMockSource().data,
          is_starred: true,
        },
      });
      renderWithProviders(<Source source={starredSource} {...defaultProps} />);

      // Find the star button by its icon
      const starButton = screen.getByRole("button");
      await user.click(starButton);

      expect(mockOnToggleStar).toHaveBeenCalledWith("test-uuid-123", true);
    });
  });

  describe("text content", () => {
    it("displays the correct journalist designation", () => {
      const source = createMockSource({
        data: {
          ...createMockSource().data,
          journalist_designation: "unique source name",
        },
      });
      renderWithProviders(<Source source={source} {...defaultProps} />);

      const designation = screen.getByTestId(
        "source-designation-test-uuid-123",
      );
      expect(designation.textContent).toBe("Unique Source Name"); // toTitleCase applied
    });
  });

  describe("memoization", () => {
    const mockSource: SourceType = {
      uuid: "source-1",
      data: {
        uuid: "source-1",
        journalist_designation: "test source",
        is_starred: false,
        last_updated: "2025-01-15T10:00:00Z",
        public_key: "test-public-key",
        fingerprint: "test-fingerprint",
      },
      isRead: true,
      hasAttachment: false,
      showMessagePreview: false,
      messagePreview: "",
    };

    const baseProps = {
      source: mockSource,
      isSelected: false,
      isActive: false,
      onSelect: mockOnSelect,
      onToggleStar: mockOnToggleStar,
      onCancelPendingStar: mockOnCancelPendingStar,
    };

    const cases: Array<[typeof baseProps, number]> = [
      // Initial render
      [baseProps, 1],
      // Same props - should not re-render
      [baseProps, 1],
      // Change isSelected - should re-render
      [{ ...baseProps, isSelected: true }, 2],
      // Change isActive - should re-render
      [{ ...baseProps, isSelected: true, isActive: true }, 3],
      // Change source data - should re-render
      [
        {
          ...baseProps,
          isSelected: true,
          isActive: true,
          source: {
            ...mockSource,
            data: { ...mockSource.data, is_starred: true },
          },
        },
        4,
      ],
      // Different source entirely - should re-render
      [
        {
          ...baseProps,
          source: {
            ...mockSource,
            uuid: "source-2",
            data: { ...mockSource.data, uuid: "source-2" },
          },
        },
        5,
      ],
    ];

    it("should handle memoization correctly", testMemoization(Source, cases));
  });
});
