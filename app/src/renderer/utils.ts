import type { TFunction } from "i18next";

/**
 * Normalize locale code from POSIX format to BCP 47 format
 * e.g., "en_US.UTF-8" -> "en-US", "fr_FR" -> "fr-FR"
 */
export function normalizeLocale(locale: string): string {
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
 * Ensures a date string is treated as UTC by appending 'Z' if no timezone is specified
 */
function ensureUtcDateString(dateString: string): string {
  // Check if timezone info is already present:
  // - 'Z' indicates UTC
  // - '+' indicates positive timezone offset
  // - '-' after position 10 indicates negative timezone offset
  //   (position check distinguishes timezone '-' from date separator hyphens in "2025-08-29")
  return dateString.includes("Z") ||
    dateString.includes("+") ||
    (dateString.includes("-") && dateString.lastIndexOf("-") > 10)
    ? dateString
    : dateString + "Z";
}

/**
 * Format a date string to show relative or absolute dates for sidebar display
 * - Today: show time (e.g., "2:30 PM")
 * - Yesterday: show "Yesterday"
 * - This year: show month and day (e.g., "10 Apr")
 * - Previous years: show month, day, and year (e.g., "10 Apr 2023")
 */
export function formatDateShort(
  dateString: string,
  locale: string,
  t: TFunction,
): string {
  const date = new Date(ensureUtcDateString(dateString));
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
 * Format a date string to show full timestamp with time for header display
 * Shows complete date with time and timezone (e.g., "April 10, 2024 at 2:30 PM PDT")
 */
export function formatDateLong(dateString: string, locale: string): string {
  const date = new Date(ensureUtcDateString(dateString));

  // Handle invalid dates
  if (isNaN(date.getTime())) {
    return "Invalid Date";
  }

  const normalizedLocale = normalizeLocale(
    locale || navigator.language || "en",
  );

  return new Intl.DateTimeFormat(normalizedLocale, {
    year: "numeric",
    month: "long",
    day: "numeric",
    hour: "numeric",
    minute: "2-digit",
    timeZoneName: "short",
  }).format(date);
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
