/**
 * Format a date string to show relative or absolute dates
 * - Today: show time (e.g., "2:30 PM")
 * - Yesterday: show "Yesterday"
 * - This year: show month and day (e.g., "10 Apr")
 * - Previous years: show month, day, and year (e.g., "10 Apr 2023")
 */
export function formatLastUpdated(dateString: string): string {
  const date = new Date(dateString);
  const now = new Date();
  const today = new Date(now.getFullYear(), now.getMonth(), now.getDate());
  const yesterday = new Date(today.getTime() - 24 * 60 * 60 * 1000);
  const currentYear = now.getFullYear();

  // Reset time to start of day for comparison
  const dateOnly = new Date(
    date.getFullYear(),
    date.getMonth(),
    date.getDate(),
  );

  if (dateOnly.getTime() === today.getTime()) {
    // Today - show time
    return date.toLocaleTimeString([], { hour: "numeric", minute: "2-digit" });
  } else if (dateOnly.getTime() === yesterday.getTime()) {
    // Yesterday
    return "Yesterday";
  } else if (date.getFullYear() === currentYear) {
    // This year - show month and day
    return date.toLocaleDateString([], { month: "short", day: "numeric" });
  } else {
    // Previous years - show month, day, and year
    return date.toLocaleDateString([], {
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
