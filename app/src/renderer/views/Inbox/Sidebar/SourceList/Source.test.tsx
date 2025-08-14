import { screen } from "@testing-library/react";
import { expect, describe, it, vi } from "vitest";
import userEvent from "@testing-library/user-event";
import { renderWithProviders } from "../../../../test-component-setup";
import Source from "./Source";
import type { Source as SourceType } from "../../../../../types";

// Mock functions for props
const mockOnSelect = vi.fn();
const mockOnToggleStar = vi.fn();
const mockOnClick = vi.fn();

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
  onClick: mockOnClick,
};

describe("Source Component", () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe("isRead functionality", () => {
    it("displays designation with bold font when source is unread", () => {
      const unreadSource = createMockSource({ isRead: false });
      renderWithProviders(<Source source={unreadSource} {...defaultProps} />);

      const designation = screen.getByTestId("source-designation");
      expect(designation.className).toContain("font-bold");
      expect(designation.className).not.toContain("font-medium");
    });

    it("displays designation with medium font when source is read", () => {
      const readSource = createMockSource({ isRead: true });
      renderWithProviders(<Source source={readSource} {...defaultProps} />);

      const designation = screen.getByTestId("source-designation");
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
        "source-checkbox",
      ) as HTMLInputElement;
      expect(checkbox.checked).toBe(true);
    });

    it("displays unchecked checkbox when isSelected is false", () => {
      const source = createMockSource();
      renderWithProviders(
        <Source source={source} {...defaultProps} isSelected={false} />,
      );

      const checkbox = screen.getByTestId(
        "source-checkbox",
      ) as HTMLInputElement;
      expect(checkbox.checked).toBe(false);
    });

    it("calls onSelect when checkbox is clicked", async () => {
      const user = userEvent.setup();
      const source = createMockSource();
      renderWithProviders(
        <Source source={source} {...defaultProps} isSelected={false} />,
      );

      const checkbox = screen.getByTestId("source-checkbox");
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
    it("calls onClick when source is clicked", async () => {
      const user = userEvent.setup();
      const source = createMockSource();
      const { container } = renderWithProviders(
        <Source source={source} {...defaultProps} />,
      );

      const sourceElement = container.firstChild as HTMLElement;
      await user.click(sourceElement);

      expect(mockOnClick).toHaveBeenCalledWith("test-uuid-123");
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

      const designation = screen.getByTestId("source-designation");
      expect(designation.textContent).toBe("Unique Source Name"); // toTitleCase applied
    });
  });
});
