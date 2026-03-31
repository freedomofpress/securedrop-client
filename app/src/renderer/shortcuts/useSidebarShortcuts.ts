import { useShortcut } from "./useShortcut";

interface SidebarShortcutHandlers {
  onSourceUp: (e: KeyboardEvent) => void;
  onSourceDown: (e: KeyboardEvent) => void;
  onSourceSelect: (e: KeyboardEvent) => void;
  onDeleteCheckedSources: (e: KeyboardEvent) => void;
  enabled: boolean;
}

/**
 * Wire up all sidebar-scoped keyboard shortcuts.
 * Pass `enabled: true` when the sidebar panel has focus.
 */
export function useSidebarShortcuts({
  onSourceUp,
  onSourceDown,
  onSourceSelect,
  onDeleteCheckedSources,
  enabled,
}: SidebarShortcutHandlers) {
  useShortcut("sourceUp", onSourceUp, { enabled });
  useShortcut("sourceDown", onSourceDown, { enabled });
  useShortcut("sourceSelect", onSourceSelect, { enabled });
  useShortcut("deleteCheckedSources", onDeleteCheckedSources, { enabled });
}
