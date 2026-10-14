import { memo, type ReactNode } from "react";

interface ActivityRowProps {
  icon: ReactNode;
  title: string;
  // Full title for the tooltip when `title` has been truncated for display
  titleTooltip?: string;
  subtitle: string;
  trailing: ReactNode;
  testId: string;
}

const ActivityRow = memo(function ActivityRow({
  icon,
  title,
  titleTooltip,
  subtitle,
  trailing,
  testId,
}: ActivityRowProps) {
  return (
    <li
      data-testid={testId}
      className="flex items-center gap-2 px-3 py-1.5 first:pt-2 last:pb-2"
    >
      <span className="flex size-4 flex-shrink-0 items-center justify-center">
        {icon}
      </span>
      <span className="flex min-w-0 flex-1 flex-col">
        <span className="truncate text-sm" title={titleTooltip} dir="auto">
          {title}
        </span>
        <span className="sd-text-tertiary truncate text-xs" dir="auto">
          {subtitle}
        </span>
      </span>
      <span className="flex flex-shrink-0 items-center">{trailing}</span>
    </li>
  );
});

export default ActivityRow;
