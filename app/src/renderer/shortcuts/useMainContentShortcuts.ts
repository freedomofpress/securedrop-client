import { useShortcut } from "./useShortcut";

interface MainContentShortcutHandlers {
  onDeleteSource: (e: KeyboardEvent) => void;
  onSendReply: (e: KeyboardEvent) => void;
  onDownloadAll: (e: KeyboardEvent) => void;
  enabled: boolean;
}

/**
 * Wire up all main content-scoped keyboard shortcuts.
 * Pass `enabled: true` when the main content panel has focus.
 */
export function useMainContentShortcuts({
  onDeleteSource,
  onSendReply,
  onDownloadAll,
  enabled,
}: MainContentShortcutHandlers) {
  useShortcut("deleteSource", onDeleteSource, { enabled });
  useShortcut("sendReply", onSendReply, { enabled });
  useShortcut("downloadAll", onDownloadAll, { enabled });
}
