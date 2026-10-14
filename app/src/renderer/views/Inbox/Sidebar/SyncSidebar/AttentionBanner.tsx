import { memo } from "react";
import { useTranslation } from "react-i18next";
import { CircleX } from "lucide-react";

import { formatFilename, toTitleCase } from "../../../../utils";
import type {
  DownloadWithStatus,
  PendingEventWithStatus,
} from "../../../../features/syncActivity/syncActivitySlice";
import { downloadReasonKey, eventReasonKey } from "./presentation";

interface AttentionBannerProps {
  events: PendingEventWithStatus[];
  downloads: DownloadWithStatus[];
}

const Banner = memo(function Banner({
  summary,
  testId,
}: {
  summary: string;
  testId: string;
}) {
  return (
    <li
      data-testid={testId}
      className="flex items-center gap-2 rounded-lg border border-red-200 bg-red-50 px-3 py-2"
    >
      <CircleX
        size={16}
        strokeWidth={1.5}
        aria-hidden="true"
        className="flex-shrink-0 text-red-500"
      />
      <span className="min-w-0 flex-1 truncate text-sm" title={summary}>
        {summary}
      </span>
    </li>
  );
});

const AttentionBanner = memo(function AttentionBanner({
  events,
  downloads,
}: AttentionBannerProps) {
  const { t } = useTranslation("Sidebar");

  if (events.length === 0 && downloads.length === 0) {
    return null;
  }

  const unknownSource = t("syncSidebar.unknownSource");

  return (
    <ul
      aria-label={t("syncSidebar.attention.heading")}
      className="flex flex-col gap-2"
    >
      {events.map((event) => (
        <Banner
          key={event.id}
          testId={`sync-attention-${event.id}`}
          summary={t("syncSidebar.attention.summary", {
            action: t(`syncSidebar.eventType.${event.type}`),
            target: event.sourceDesignation
              ? toTitleCase(event.sourceDesignation)
              : unknownSource,
            reason: t(eventReasonKey(event.lastEventStatus)),
          })}
        />
      ))}
      {downloads.map((download) => (
        <Banner
          key={download.itemUuid}
          testId={`sync-attention-${download.itemUuid}`}
          summary={t("syncSidebar.attention.summary", {
            action: download.filename
              ? formatFilename(
                  download.filename.substring(
                    download.filename.lastIndexOf("/") + 1,
                  ),
                  24,
                  6,
                )
              : t("syncSidebar.encryptedFile"),
            target: download.sourceDesignation
              ? toTitleCase(download.sourceDesignation)
              : unknownSource,
            reason: t(downloadReasonKey(download.fetchStatus)),
          })}
        />
      ))}
    </ul>
  );
});

export default AttentionBanner;
