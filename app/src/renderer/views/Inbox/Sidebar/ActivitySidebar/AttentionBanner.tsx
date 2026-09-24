import { memo } from "react";
import { useTranslation } from "react-i18next";
import { CircleX } from "lucide-react";

import { formatFilename, toTitleCase } from "../../../../utils";
import type { DownloadWithStatus } from "../../../../features/activity/activitySlice";
import { FetchStatus } from "../../../../../types";

interface AttentionBannerProps {
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
  downloads,
}: AttentionBannerProps) {
  const { t } = useTranslation("Sidebar");

  if (downloads.length === 0) {
    return null;
  }

  const unknownSource = t("activitySidebar.unknownSource");

  return (
    <ul
      aria-label={t("activitySidebar.attention.heading")}
      className="flex flex-col gap-2"
    >
      {downloads.map((download) => (
        <Banner
          key={download.itemUuid}
          testId={`sync-attention-${download.itemUuid}`}
          summary={t("activitySidebar.attention.summary", {
            action: download.filename
              ? formatFilename(
                  download.filename.substring(
                    download.filename.lastIndexOf("/") + 1,
                  ),
                  24,
                  6,
                )
              : t("activitySidebar.encryptedFile"),
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

const downloadReasonKey = (status: FetchStatus): string => {
  switch (status) {
    case FetchStatus.FailedDownloadRetryable:
      return "activitySidebar.attentionReason.downloadRetrying";
    case FetchStatus.FailedDecryptionRetryable:
      return "activitySidebar.attentionReason.decryptionRetrying";
    default:
      return "activitySidebar.attentionReason.downloadFailed";
  }
};

export default AttentionBanner;
