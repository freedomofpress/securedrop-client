import { useShortcut } from "./useShortcut";

interface GlobalShortcutHandlers {
  onQuit: (e: KeyboardEvent) => void;
  onFocusSidebar: (e: KeyboardEvent) => void;
  onFocusMainContent: (e: KeyboardEvent) => void;
  onOpenHelp: (e: KeyboardEvent) => void;
  onSync: (e: KeyboardEvent) => void;
  onSignOut: (e: KeyboardEvent) => void;
}

/**
 * Wire up all global keyboard shortcuts.
 * These fire regardless of which panel has focus.
 */
export function useGlobalShortcuts({
  onQuit,
  onFocusSidebar,
  onFocusMainContent,
  onOpenHelp,
  onSync,
  onSignOut,
}: GlobalShortcutHandlers) {
  useShortcut("quit", onQuit);
  useShortcut("focusSidebar", onFocusSidebar);
  useShortcut("focusMainContent", onFocusMainContent);
  useShortcut("openHelp", onOpenHelp);
  useShortcut("sync", onSync);
  useShortcut("signOut", onSignOut);
}
