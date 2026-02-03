import { useState, useMemo, memo } from "react";
import { useTranslation } from "react-i18next";

interface TruncatedTextProps {
  text: string;
  maxCodePoints?: number;
  className?: string;
}

/**
 * Truncates text at a specified number of Unicode code points, with
 * "See more" / "See less" toggle functionality.
 *
 * Uses code points (not JS string length) to handle emoji and other
 * multi-byte characters correctly.
 */
const TruncatedText = memo(function TruncatedText({
  text,
  maxCodePoints = 1000,
  className,
}: TruncatedTextProps) {
  const { t } = useTranslation("common");
  const [expanded, setExpanded] = useState(false);

  // Convert to code points array for accurate counting/slicing
  const codePoints = useMemo(() => [...text], [text]);
  const needsTruncation = codePoints.length > maxCodePoints;

  const displayText = useMemo(() => {
    if (!needsTruncation || expanded) {
      return text;
    }

    // Get first maxCodePoints code points
    const truncated = codePoints.slice(0, maxCodePoints).join("");

    // Try to truncate at a word boundary (space, newline) for cleaner display
    const lastSpace = truncated.lastIndexOf(" ");
    const lastNewline = truncated.lastIndexOf("\n");
    const lastBreak = Math.max(lastSpace, lastNewline);

    // Only use word boundary if it's reasonably close to the end (within 100 chars)
    // Compare against truncated.length to handle emoji/surrogate pairs correctly
    // Guard: lastBreak must be > 0 to avoid empty string (when break is at start or not found)
    if (lastBreak > 0 && lastBreak > truncated.length - 100) {
      return truncated.slice(0, lastBreak);
    }

    return truncated;
  }, [text, codePoints, maxCodePoints, expanded, needsTruncation]);

  if (!needsTruncation) {
    return <span className={className}>{text}</span>;
  }

  return (
    <span className={className}>
      {displayText}
      {!expanded && `${t("ellipsis")} `}
      <button
        type="button"
        onClick={() => setExpanded(!expanded)}
        aria-expanded={expanded}
        className="text-blue-600 hover:underline focus:outline-none focus:ring-2 focus:ring-blue-500 focus:ring-offset-2 rounded"
      >
        {expanded ? t("seeLess") : t("seeMore")}
      </button>
    </span>
  );
});

export default TruncatedText;
