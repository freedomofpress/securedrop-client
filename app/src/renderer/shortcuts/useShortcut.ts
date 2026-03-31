import { useHotkeys, type Options } from "react-hotkeys-hook";

import { getShortcut } from "./shortcutDefinitions";

/**
 * Input types that are NOT text-entry fields. Shortcuts should fire when
 * these are focused (e.g. a checkbox inside a source row).
 */
const NON_TEXT_INPUT_TYPES = new Set([
  "checkbox",
  "radio",
  "button",
  "submit",
  "reset",
  "image",
  "file",
  "color",
  "range",
]);

/**
 * Determine whether a keyboard event should be ignored by shortcuts.
 *
 * react-hotkeys-hook's built-in form-tag blocklist is too coarse — it blocks
 * events from checkboxes, elements with role="option", etc. We disable that
 * blocklist (via enableOnFormTags: true) and use this function instead.
 *
 * Rules:
 * 1. Non-text form elements (checkbox, radio, button, role="option") → allow
 * 2. Text-entry elements (text input, textarea, contentEditable) → block,
 *    UNLESS the shortcut's registry entry explicitly enables that tag via
 *    its own enableOnFormTags array (e.g. sendReply enables TEXTAREA).
 */
function shouldIgnoreEvent(
  event: KeyboardEvent,
  registryEnableOnFormTags?: readonly string[] | boolean,
): boolean {
  const target = event.target as HTMLElement;
  if (!target?.tagName) {
    return false;
  }

  const tag = target.tagName.toLowerCase();

  // Check if this shortcut explicitly enables on this element's tag/role
  if (registryEnableOnFormTags === true) {
    return false;
  }
  if (Array.isArray(registryEnableOnFormTags)) {
    const role = target.getAttribute("role");
    if (
      registryEnableOnFormTags.some(
        (t) => t.toLowerCase() === tag || t.toLowerCase() === role,
      )
    ) {
      return false;
    }
  }

  // Block text-entry elements
  if (tag === "textarea" || tag === "select") {
    return true;
  }
  if (tag === "input") {
    const type = (target as HTMLInputElement).type?.toLowerCase() ?? "text";
    return !NON_TEXT_INPUT_TYPES.has(type);
  }
  if (target.isContentEditable) {
    return true;
  }

  return false;
}

/**
 * Bind a registered shortcut by its id.
 * The key combination and default options come from the central registry.
 * The callback and deps are provided by the calling component.
 */
export function useShortcut<T extends HTMLElement = HTMLElement>(
  id: string,
  callback: (e: KeyboardEvent) => void,
  extraOptions?: Partial<Options>,
  deps?: unknown[],
) {
  const shortcut = getShortcut(id);
  const options: Options = {
    ...shortcut.options,
    ...extraOptions,
    // Disable react-hotkeys-hook's built-in form-tag blocking; we handle it via ignoreEventWhen
    enableOnFormTags: true,
    ignoreEventWhen: (e) =>
      shouldIgnoreEvent(e, shortcut.options?.enableOnFormTags),
  };
  return useHotkeys<T>(shortcut.keys, callback, options, deps);
}
