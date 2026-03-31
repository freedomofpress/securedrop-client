/**
 * Imperative handle to open the keyboard help modal from anywhere
 * (e.g. F1 keyboard shortcut, menu item).
 *
 * The KeyboardHelpModal component sets this when it mounts and clears it on unmount.
 */
let showHelpModal: (() => void) | null = null;

export function requestHelp() {
  showHelpModal?.();
}

export function setHelpHandler(handler: (() => void) | null) {
  showHelpModal = handler;
}
