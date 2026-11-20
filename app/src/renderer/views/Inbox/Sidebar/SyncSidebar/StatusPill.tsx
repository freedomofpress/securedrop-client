import { memo } from "react";

export type PillTone = "neutral" | "warning" | "danger";

const TONE_CLASS: Record<PillTone, string> = {
  neutral: "border-gray-200 text-gray-600",
  warning: "border-amber-400 text-amber-600",
  danger: "border-red-300 text-red-600",
};

const DOT_CLASS: Record<PillTone, string> = {
  neutral: "bg-gray-400",
  warning: "bg-amber-500",
  danger: "bg-red-500",
};

interface StatusPillProps {
  label: string;
  tone: PillTone;
}

const StatusPill = memo(function StatusPill({ label, tone }: StatusPillProps) {
  return (
    <span
      data-testid="sync-status-pill"
      data-tone={tone}
      className={`sd-bg-primary flex items-center gap-1.5 rounded-md border px-2 py-0.5 text-xs whitespace-nowrap ${TONE_CLASS[tone]}`}
    >
      <span
        aria-hidden="true"
        className={`size-1.5 rounded-full ${DOT_CLASS[tone]}`}
      />
      {label}
    </span>
  );
});

export default StatusPill;
