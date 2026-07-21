import { describe, it, expect } from "vitest";
import { screen } from "@testing-library/react";
import KeyboardHelp from "./KeyboardHelp";
import { shortcuts } from "../../../../shortcuts/shortcutDefinitions";
import { renderWithProviders } from "../../../../test-component-setup";

describe("KeyboardHelp", () => {
  it("renders all shortcuts from the registry", () => {
    renderWithProviders(<KeyboardHelp />);

    // Every shortcut's display keys should appear as <kbd> elements
    const allKbdElements = document.querySelectorAll("kbd");
    const kbdTexts = Array.from(allKbdElements).map((el) => el.textContent);

    for (const shortcut of shortcuts) {
      for (const chord of shortcut.displayKeys) {
        for (const key of chord) {
          expect(kbdTexts).toContain(key);
        }
      }
    }
  });

  it("renders the correct total number of shortcuts", () => {
    renderWithProviders(<KeyboardHelp />);

    // Each shortcut gets a row with description text
    // Count rows by the description class
    const rows = document.querySelectorAll(
      ".flex.items-center.justify-between.py-\\[5px\\]",
    );
    expect(rows.length).toBe(shortcuts.length);
  });

  it("renders category headings", () => {
    renderWithProviders(<KeyboardHelp />);

    const expectedCategories = [
      "Application",
      "Navigation",
      "Sources",
      "Composing",
      "Files",
    ];

    for (const category of expectedCategories) {
      expect(screen.getByText(category)).toBeInTheDocument();
    }
  });

  it("renders the header title", () => {
    renderWithProviders(<KeyboardHelp />);

    expect(screen.getByText("Keyboard shortcuts")).toBeInTheDocument();
  });

  it("groups shortcuts by category", () => {
    renderWithProviders(<KeyboardHelp />);

    const uniqueCategories = new Set(shortcuts.map((s) => s.categoryKey));
    const headings = document.querySelectorAll(
      ".uppercase.tracking-\\[0\\.06em\\]",
    );
    expect(headings.length).toBe(uniqueCategories.size);
  });
});
