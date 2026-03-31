/**
 * Imperative handle to open the quit confirmation modal from anywhere
 * (e.g. keyboard shortcut callbacks).
 *
 * The QuitModal component sets this when it mounts and clears it on unmount.
 */
let showQuitModal: (() => void) | null = null;

export function requestQuit() {
  showQuitModal?.();
}

export function setQuitHandler(handler: (() => void) | null) {
  showQuitModal = handler;
}
