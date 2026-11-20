import { memo } from "react";
import { useTranslation } from "react-i18next";
import { Check, RefreshCw } from "lucide-react";

import { toTitleCase } from "../../../../utils";
import {
  PendingEventDisplayStatus,
  type CompletedEventActivity,
  type PendingEventWithStatus,
} from "../../../../features/syncActivity/syncActivitySlice";
import ActivityRow from "./ActivityRow";
import StatusPill from "./StatusPill";
import { EVENT_PRESENTATION } from "./presentation";

interface PendingEventRowProps {
  event: PendingEventWithStatus;
}

export const CompletedEventRow = memo(function CompletedEventRow({
  event,
}: {
  event: CompletedEventActivity;
}) {
  const { t } = useTranslation("Sidebar");
  const Icon = EVENT_PRESENTATION[event.type];

  return (
    <ActivityRow
      testId={`sync-event-${event.id}`}
      icon={
        <Icon
          size={16}
          strokeWidth={1.5}
          aria-hidden="true"
          className="sd-text-tertiary"
        />
      }
      title={t(`syncSidebar.eventType.${event.type}`)}
      subtitle={designationOf(event.sourceDesignation, t)}
      trailing={
        <span
          data-testid="sync-event-done"
          className="sd-text-tertiary flex items-center gap-1.5 text-sm"
        >
          <Check size={14} strokeWidth={2} aria-hidden="true" />
          {t("syncSidebar.eventStatus.done")}
        </span>
      }
    />
  );
});

const designationOf = (
  sourceDesignation: string | null,
  t: (key: string) => string,
) =>
  sourceDesignation
    ? toTitleCase(sourceDesignation)
    : t("syncSidebar.unknownSource");

const PendingEventRow = memo(function PendingEventRow({
  event,
}: PendingEventRowProps) {
  const { t } = useTranslation("Sidebar");
  const Icon = EVENT_PRESENTATION[event.type];
  const sending = event.displayStatus === PendingEventDisplayStatus.SENDING;

  return (
    <ActivityRow
      testId={`sync-event-${event.id}`}
      icon={
        <Icon
          size={16}
          strokeWidth={1.5}
          aria-hidden="true"
          className="sd-text-tertiary"
        />
      }
      title={t(`syncSidebar.eventType.${event.type}`)}
      subtitle={designationOf(event.sourceDesignation, t)}
      trailing={
        sending ? (
          <span className="flex items-center gap-1.5 text-sm text-blue-600">
            <RefreshCw
              size={14}
              strokeWidth={1.5}
              aria-hidden="true"
              className="animate-spin"
            />
            {t("syncSidebar.eventStatus.sending")}
          </span>
        ) : (
          <StatusPill
            label={t(`syncSidebar.eventStatus.${event.displayStatus}`)}
            tone="neutral"
          />
        )
      }
    />
  );
});

export default PendingEventRow;
