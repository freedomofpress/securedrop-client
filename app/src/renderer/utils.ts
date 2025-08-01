import type { TFunction } from "i18next";

/**
 * Normalize locale code from POSIX format to BCP 47 format
 * e.g., "en_US.UTF-8" -> "en-US", "fr_FR" -> "fr-FR"
 */
function normalizeLocale(locale: string): string {
  // Remove encoding part (e.g., .UTF-8)
  const withoutEncoding = locale.split(".")[0];

  // Convert underscore to hyphen for BCP 47 format
  const normalized = withoutEncoding.replace("_", "-");

  // Validate the locale by trying to create an Intl object
  try {
    new Intl.DateTimeFormat(normalized);
    return normalized;
  } catch {
    // If invalid, extract just the language code
    const languageCode = normalized.split("-")[0];
    try {
      new Intl.DateTimeFormat(languageCode);
      return languageCode;
    } catch {
      // Ultimate fallback
      return "en";
    }
  }
}

/**
 * Format a date string to show relative or absolute dates
 * - Today: show time (e.g., "2:30 PM")
 * - Yesterday: show "Yesterday"
 * - This year: show month and day (e.g., "10 Apr")
 * - Previous years: show month, day, and year (e.g., "10 Apr 2023")
 */
export function formatDate(
  dateString: string,
  locale: string,
  t: TFunction,
): string {
  const date = new Date(dateString);
  const now = new Date();
  const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const yesterday = new Date(today.getTime() - 24 * 60 * 60 * 1000);
  const currentYear = now.getFullYear();

  // Normalize and default to browser locale if not provided
  const dateLocale = normalizeLocale(locale || navigator.language || "en");

  // Reset time to start of day for comparison
  const dateOnly = new Date(
    date.getFullYear(),
    date.getMonth(),
    date.getDate(),
  );

  if (dateOnly.getTime() === today.getTime()) {
    // Today - show time
    return date.toLocaleTimeString(dateLocale, {
      hour: "numeric",
      minute: "2-digit",
    });
  } else if (dateOnly.getTime() === yesterday.getTime()) {
    // Yesterday
    return t ? t("yesterday") : "Yesterday";
  } else if (date.getFullYear() === currentYear) {
    // This year - show month and day
    return date.toLocaleDateString(dateLocale, {
      month: "short",
      day: "numeric",
    });
  } else {
    // Previous years - show month, day, and year
    return date.toLocaleDateString(dateLocale, {
      month: "short",
      day: "numeric",
      year: "numeric",
    });
  }
}

/**
 * Get initials from a name string
 */
export function getInitials(name: string): string {
  return name
    .split(" ")
    .map((word) => word.charAt(0).toUpperCase())
    .join("")
    .substring(0, 2); // Limit to 2 characters
}

/**
 * Convert string to title case
 */
export function toTitleCase(str: string): string {
  return str.replace(
    /\w\S*/g,
    (txt) => txt.charAt(0).toUpperCase() + txt.substr(1).toLowerCase(),
  );
}
