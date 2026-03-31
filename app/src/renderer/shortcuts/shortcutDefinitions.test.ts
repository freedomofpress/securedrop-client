import { describe, it, expect } from "vitest";

import {
  shortcuts,
  getShortcut,
  getShortcutsByScope,
  Scope,
} from "./shortcutDefinitions";

describe("shortcutDefinitions", () => {
  it("has no duplicate ids", () => {
    const ids = shortcuts.map((s) => s.id);
    expect(new Set(ids).size).toBe(ids.length);
  });

  it("has no duplicate keys within the same scope", () => {
    const seen = new Map<string, string>();
    for (const s of shortcuts) {
      const key = `${s.scope}:${s.keys}`;
      expect(
        seen.has(key),
        `Duplicate key "${s.keys}" in scope "${s.scope}" (ids: "${seen.get(key)}" and "${s.id}")`,
      ).toBe(false);
      seen.set(key, s.id);
    }
  });

  it("every shortcut has non-empty required fields", () => {
    for (const s of shortcuts) {
      expect(s.id).toBeTruthy();
      expect(s.keys).toBeTruthy();
      expect(s.descriptionKey).toBeTruthy();
      expect(s.categoryKey).toBeTruthy();
      expect(s.scope).toBeTruthy();
      expect(s.displayKeys.length).toBeGreaterThan(0);
    }
  });

  describe("getShortcut", () => {
    it("returns a shortcut by id", () => {
      const s = getShortcut("quit");
      expect(s.id).toBe("quit");
      expect(s.keys).toBe("ctrl+q");
    });

    it("throws for unknown id", () => {
      expect(() => getShortcut("nonexistent")).toThrow(
        "Unknown shortcut: nonexistent",
      );
    });
  });

  describe("getShortcutsByScope", () => {
    it("returns only global shortcuts", () => {
      const global = getShortcutsByScope(Scope.GLOBAL);
      expect(global.length).toBeGreaterThan(0);
      expect(global.every((s) => s.scope === Scope.GLOBAL)).toBe(true);
    });

    it("returns only sidebar shortcuts", () => {
      const sidebar = getShortcutsByScope(Scope.SIDEBAR);
      expect(sidebar.length).toBeGreaterThan(0);
      expect(sidebar.every((s) => s.scope === Scope.SIDEBAR)).toBe(true);
    });

    it("returns only mainContent shortcuts", () => {
      const main = getShortcutsByScope(Scope.MAIN_CONTENT);
      expect(main.length).toBeGreaterThan(0);
      expect(main.every((s) => s.scope === Scope.MAIN_CONTENT)).toBe(true);
    });

    it("returns all shortcuts across all scopes", () => {
      const all = [
        ...getShortcutsByScope(Scope.GLOBAL),
        ...getShortcutsByScope(Scope.SIDEBAR),
        ...getShortcutsByScope(Scope.MAIN_CONTENT),
      ];
      expect(all.length).toBe(shortcuts.length);
    });
  });
});
