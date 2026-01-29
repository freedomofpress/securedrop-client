import { screen } from "@testing-library/react";
import { expect, describe, it } from "vitest";
import userEvent from "@testing-library/user-event";
import { renderWithProviders, testMemoization } from "../test-component-setup";
import TruncatedText from "./TruncatedText";

describe("TruncatedText Component Memoization", () => {
  const cases: Array<[{ text: string; maxCodePoints?: number }, number]> = [
    // Initial render
    [{ text: "Hello world" }, 1],
    // Same props - should not re-render
    [{ text: "Hello world" }, 1],
    // Change text - should re-render
    [{ text: "Different text" }, 2],
    // Change maxCodePoints - should re-render
    [{ text: "Different text", maxCodePoints: 100 }, 3],
    // Same props as previous - should not re-render
    [{ text: "Different text", maxCodePoints: 100 }, 3],
  ];

  it(
    "should handle memoization correctly",
    testMemoization(TruncatedText, cases),
  );
});

describe("TruncatedText Component", () => {
  describe("short text (no truncation needed)", () => {
    it("renders the full text without See more button", () => {
      const shortText = "This is a short message.";
      renderWithProviders(<TruncatedText text={shortText} />);

      expect(screen.getByText(shortText)).toBeDefined();
      expect(screen.queryByText("See more")).toBeNull();
      expect(screen.queryByText("See less")).toBeNull();
    });

    it("renders empty string without crashing", () => {
      renderWithProviders(<TruncatedText text="" />);
      expect(screen.queryByText("See more")).toBeNull();
    });
  });

  describe("long text (truncation needed)", () => {
    const longText = "a".repeat(3500);

    it("truncates text and shows See more button", () => {
      renderWithProviders(<TruncatedText text={longText} />);

      // Should not show the full text
      expect(screen.queryByText(longText)).toBeNull();
      // Should show See more button
      expect(screen.getByText("See more")).toBeDefined();
      // Should show ellipsis
      expect(screen.getByText("…", { exact: false })).toBeDefined();
    });

    it("expands text when See more is clicked", async () => {
      const user = userEvent.setup();
      renderWithProviders(<TruncatedText text={longText} />);

      const seeMoreButton = screen.getByText("See more");
      await user.click(seeMoreButton);

      // Should now show full text
      expect(screen.getByText(longText)).toBeDefined();
      // Should show See less button
      expect(screen.getByText("See less")).toBeDefined();
      // Should not show See more button
      expect(screen.queryByText("See more")).toBeNull();
    });

    it("collapses text when See less is clicked", async () => {
      const user = userEvent.setup();
      renderWithProviders(<TruncatedText text={longText} />);

      // Expand first
      await user.click(screen.getByText("See more"));
      expect(screen.getByText(longText)).toBeDefined();

      // Then collapse
      await user.click(screen.getByText("See less"));

      // Should be truncated again
      expect(screen.queryByText(longText)).toBeNull();
      expect(screen.getByText("See more")).toBeDefined();
    });
  });

  describe("custom maxCodePoints", () => {
    it("respects custom maxCodePoints value", () => {
      const text = "a".repeat(200);
      renderWithProviders(<TruncatedText text={text} maxCodePoints={100} />);

      // Should be truncated at 100 chars
      expect(screen.queryByText(text)).toBeNull();
      expect(screen.getByText("See more")).toBeDefined();
    });

    it("does not truncate when text is under custom maxCodePoints", () => {
      const text = "a".repeat(50);
      renderWithProviders(<TruncatedText text={text} maxCodePoints={100} />);

      expect(screen.getByText(text)).toBeDefined();
      expect(screen.queryByText("See more")).toBeNull();
    });
  });

  describe("Unicode handling", () => {
    it("counts emoji as single code points, not JS string length", () => {
      // Each emoji is 1 code point but 2 JS chars (surrogate pair)
      // 150 emojis = 150 code points = 300 JS chars
      const emojiText = "👋".repeat(150);
      expect(emojiText.length).toBe(300); // JS length is 300

      // With maxCodePoints=100, should truncate at 100 emojis (200 JS chars)
      renderWithProviders(
        <TruncatedText text={emojiText} maxCodePoints={100} />,
      );

      expect(screen.getByText("See more")).toBeDefined();

      // The truncated text should have 100 emojis
      const truncatedEmojis = "👋".repeat(100);
      expect(screen.getByText(truncatedEmojis, { exact: false })).toBeDefined();
    });

    it("handles mixed ASCII and emoji correctly", () => {
      // "Hi 👋 " is 5 code points: H, i, space, 👋, space
      const mixedText = "Hi 👋 ".repeat(100); // 500 code points
      renderWithProviders(
        <TruncatedText text={mixedText} maxCodePoints={50} />,
      );

      expect(screen.getByText("See more")).toBeDefined();
    });

    it("does not corrupt emoji when truncating", async () => {
      const user = userEvent.setup();
      const emojiText = "👋".repeat(150);

      renderWithProviders(
        <TruncatedText text={emojiText} maxCodePoints={100} />,
      );

      // Expand to see full text
      await user.click(screen.getByText("See more"));

      // Full emoji text should be intact
      expect(screen.getByText(emojiText)).toBeDefined();
    });
  });

  describe("word boundary truncation", () => {
    it("truncates at word boundary when space is near the end", () => {
      // Create text that has a space near the truncation point
      // 610 repetitions of "word " = 3050 code points, truncated at 3000
      // Should find a space and truncate there
      const text = "word ".repeat(610);
      renderWithProviders(<TruncatedText text={text} maxCodePoints={3000} />);

      expect(screen.getByText("See more")).toBeDefined();
      // The truncated text should end cleanly (no partial "word")
      // We can't easily verify the exact truncation point, but we verify it truncates
    });

    it("truncates mid-word when no space near boundary", () => {
      // Text with no spaces - should truncate exactly at maxCodePoints
      const text = "a".repeat(3500);
      renderWithProviders(<TruncatedText text={text} maxCodePoints={3000} />);

      expect(screen.getByText("See more")).toBeDefined();
    });

    it("handles text with space only at position 0 without returning empty", () => {
      // Edge case: space at position 0, small maxCodePoints
      // Should not truncate to empty string when lastBreak is 0
      const text = " " + "a".repeat(150);
      const { container } = renderWithProviders(
        <TruncatedText text={text} maxCodePoints={50} />,
      );

      expect(screen.getByText("See more")).toBeDefined();
      // Should show 50 chars (space + 49 a's), not empty string
      // Use textContent check since testing-library normalizes whitespace
      const span = container.querySelector("span");
      expect(span?.textContent).toContain("a".repeat(49));
    });

    it("handles text with no spaces and small maxCodePoints", () => {
      // Edge case: no spaces at all, lastBreak would be -1
      // -1 > (50 - 100) = -1 > -50 = true without the guard
      const text = "a".repeat(150);
      renderWithProviders(<TruncatedText text={text} maxCodePoints={50} />);

      expect(screen.getByText("See more")).toBeDefined();
      // Should show exactly 50 chars, not 49 (slice(0, -1) bug)
      const expectedTruncated = "a".repeat(50);
      expect(
        screen.getByText(expectedTruncated, { exact: false }),
      ).toBeDefined();
    });
  });

  describe("className prop", () => {
    it("applies custom className to wrapper span for short text", () => {
      const { container } = renderWithProviders(
        <TruncatedText text="Hello" className="custom-class" />,
      );

      const span = container.querySelector(".custom-class");
      expect(span).not.toBeNull();
    });

    it("applies custom className to wrapper span when text is truncated", () => {
      const longText = "a".repeat(200);
      const { container } = renderWithProviders(
        <TruncatedText
          text={longText}
          maxCodePoints={100}
          className="custom-class"
        />,
      );

      const span = container.querySelector(".custom-class");
      expect(span).not.toBeNull();
      // Verify truncation is active
      expect(screen.getByText("See more")).toBeDefined();
    });
  });
});
