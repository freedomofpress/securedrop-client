import type { Options } from "react-hotkeys-hook";

export const Scope = {
  GLOBAL: "global",
  SIDEBAR: "sidebar",
  MAIN_CONTENT: "mainContent",
} as const;

export type ShortcutScope = (typeof Scope)[keyof typeof Scope];

export interface ShortcutDefinition {
  /** Unique identifier, used as a stable key */
  id: string;
  /** react-hotkeys-hook key string (e.g. "ctrl+q", "up") */
  keys: string;
  /** i18n key for human-readable description (resolved via t() in the help modal) */
  descriptionKey: string;
  /** i18n key for category heading (resolved via t() in the help modal) */
  categoryKey: string;
  /** Which scope(s) this shortcut is active in */
  scope: ShortcutScope;
  /** Display keys for the help modal (e.g. [["Ctrl", "Q"]]) */
  displayKeys: string[][];
  /** react-hotkeys-hook options to merge (e.g. enableOnFormTags) */
  options?: Partial<Options>;
}

export const shortcuts: ShortcutDefinition[] = [
  // === Global ===
  {
    id: "quit",
    keys: "ctrl+q",
    descriptionKey: "shortcuts.quit",
    categoryKey: "shortcuts.categories.application",
    scope: Scope.GLOBAL,
    displayKeys: [["Ctrl", "Q"]],
    options: { preventDefault: true },
  },
  {
    id: "focusSidebar",
    keys: "left",
    descriptionKey: "shortcuts.focusSidebar",
    categoryKey: "shortcuts.categories.navigation",
    scope: Scope.GLOBAL,
    displayKeys: [["←"]],
  },
  {
    id: "focusMainContent",
    keys: "right",
    descriptionKey: "shortcuts.focusMainContent",
    categoryKey: "shortcuts.categories.navigation",
    scope: Scope.GLOBAL,
    displayKeys: [["→"]],
  },
  {
    id: "openHelp",
    keys: "f1",
    descriptionKey: "shortcuts.openHelp",
    categoryKey: "shortcuts.categories.application",
    scope: Scope.GLOBAL,
    displayKeys: [["F1"]],
    options: { preventDefault: true },
  },
  {
    id: "sync",
    keys: "ctrl+s",
    descriptionKey: "shortcuts.sync",
    categoryKey: "shortcuts.categories.application",
    scope: Scope.GLOBAL,
    displayKeys: [["Ctrl", "S"]],
    options: { preventDefault: true },
  },
  {
    id: "signOut",
    keys: "ctrl+shift+o",
    descriptionKey: "shortcuts.signOut",
    categoryKey: "shortcuts.categories.application",
    scope: Scope.GLOBAL,
    displayKeys: [["Ctrl", "Shift", "O"]],
    options: { preventDefault: true },
  },
  // === Sidebar ===
  {
    id: "sourceUp",
    keys: "up",
    descriptionKey: "shortcuts.sourceUp",
    categoryKey: "shortcuts.categories.sources",
    scope: Scope.SIDEBAR,
    displayKeys: [["↑"]],
    options: { preventDefault: true },
  },
  {
    id: "sourceDown",
    keys: "down",
    descriptionKey: "shortcuts.sourceDown",
    categoryKey: "shortcuts.categories.sources",
    scope: Scope.SIDEBAR,
    displayKeys: [["↓"]],
    options: { preventDefault: true },
  },
  {
    id: "sourceSelect",
    keys: "enter, space",
    descriptionKey: "shortcuts.sourceSelect",
    categoryKey: "shortcuts.categories.sources",
    scope: Scope.SIDEBAR,
    displayKeys: [["Enter"], ["Space"]],
  },
  {
    id: "deleteCheckedSources",
    keys: "delete",
    descriptionKey: "shortcuts.deleteCheckedSources",
    categoryKey: "shortcuts.categories.sources",
    scope: Scope.SIDEBAR,
    displayKeys: [["Delete"]],
  },
  // === MainContent ===
  {
    id: "deleteSource",
    keys: "ctrl+delete",
    descriptionKey: "shortcuts.deleteSource",
    categoryKey: "shortcuts.categories.sources",
    scope: Scope.MAIN_CONTENT,
    displayKeys: [["Ctrl", "Delete"]],
  },
  {
    id: "sendReply",
    keys: "ctrl+enter",
    descriptionKey: "shortcuts.sendReply",
    categoryKey: "shortcuts.categories.composing",
    scope: Scope.MAIN_CONTENT,
    displayKeys: [["Ctrl", "Enter"]],
    options: { enableOnFormTags: ["TEXTAREA"] },
  },
  {
    id: "downloadAll",
    keys: "ctrl+d",
    descriptionKey: "shortcuts.downloadAll",
    categoryKey: "shortcuts.categories.files",
    scope: Scope.MAIN_CONTENT,
    displayKeys: [["Ctrl", "D"]],
    options: { preventDefault: true },
  },
];

/** Look up a shortcut by its stable id */
export function getShortcut(id: string): ShortcutDefinition {
  const s = shortcuts.find((s) => s.id === id);
  if (!s) {
    throw new Error(`Unknown shortcut: ${id}`);
  }
  return s;
}

/** Get all shortcuts for a given scope */
export function getShortcutsByScope(
  scope: ShortcutScope,
): ShortcutDefinition[] {
  return shortcuts.filter((s) => s.scope === scope);
}

/** Format a shortcut's displayKeys for use as a menu label, e.g. "Ctrl+Shift+O" */
export function formatDisplayKeys(def: ShortcutDefinition): string {
  return def.displayKeys.map((combo) => combo.join("+")).join(" / ");
}
