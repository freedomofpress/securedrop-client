import { memo, useCallback } from "react";
import { useTranslation } from "react-i18next";

import { getFileIconAndColor } from "../../MainContent/Conversation/Item/fileIcons";
import { formatFilename, toTitleCase } from "../../../../utils";
import {
  DownloadDisplayStatus,
  type DownloadWithStatus,
} from "../../../../features/syncActivity/syncActivitySlice";
import type { DownloadActivity } from "../../../../../types";
import ActivityRow from "./ActivityRow";
import StatusPill, { type PillTone } from "./StatusPill";
import { downloadPercent } from "./presentation";

// Filenames are middle-truncated so the extension stays visible in the
// narrow sidebar
const FILENAME_MAX_LENGTH = 28;
const FILENAME_END_LENGTH = 6;

const PILL_TONE: Record<DownloadDisplayStatus, PillTone> = {
  [DownloadDisplayStatus.QUEUED]: "neutral",
  [DownloadDisplayStatus.DOWNLOADING]: "neutral",
  [DownloadDisplayStatus.DECRYPTING]: "neutral",
  [DownloadDisplayStatus.STOPPED]: "warning",
  [DownloadDisplayStatus.NEEDS_ATTENTION]: "danger",
};

const basename = (path: string) => path.substring(path.lastIndexOf("/") + 1);

const DownloadIcon = memo(function DownloadIcon({
  filename,
}: {
  filename: string;
}) {
  const { Icon, color } = getFileIconAndColor(filename);
  return <Icon style={{ fontSize: 16, color }} />;
});

interface DownloadRowProps {
  download: DownloadWithStatus;
}

export const DownloadRow = memo(function DownloadRow({
  download,
}: DownloadRowProps) {
  const { t } = useTranslation("Sidebar");

  const filename = download.filename ? basename(download.filename) : null;
  const percent =
    download.displayStatus === DownloadDisplayStatus.DOWNLOADING
      ? downloadPercent(download.fetchProgress, download.size)
      : null;

  return (
    <ActivityRow
      testId={`sync-download-${download.itemUuid}`}
      icon={<DownloadIcon filename={filename ?? ""} />}
      title={
        filename
          ? formatFilename(filename, FILENAME_MAX_LENGTH, FILENAME_END_LENGTH)
          : t("syncSidebar.encryptedFile")
      }
      titleTooltip={filename ?? undefined}
      subtitle={designationOf(download, t)}
      trailing={
        percent !== null ? (
          <span
            className="sd-text-tertiary text-sm"
            aria-label={t("syncSidebar.download.percentLabel", { percent })}
          >
            {t("syncSidebar.download.percent", { percent })}
          </span>
        ) : (
          <StatusPill
            label={t(`syncSidebar.downloadStatus.${download.displayStatus}`)}
            tone={PILL_TONE[download.displayStatus]}
          />
        )
      }
    />
  );
});

interface CompletedDownloadRowProps {
  download: DownloadActivity;
}

export const CompletedDownloadRow = memo(function CompletedDownloadRow({
  download,
}: CompletedDownloadRowProps) {
  const { t } = useTranslation("Sidebar");
  const filename = basename(download.filename ?? "");

  const handleOpen = useCallback(() => {
    window.electronAPI.openFile(download.itemUuid).catch((error) => {
      console.error("Failed to open file:", error);
    });
  }, [download.itemUuid]);

  return (
    <ActivityRow
      testId={`sync-download-${download.itemUuid}`}
      icon={<DownloadIcon filename={filename} />}
      title={formatFilename(filename, FILENAME_MAX_LENGTH, FILENAME_END_LENGTH)}
      titleTooltip={filename}
      subtitle={designationOf(download, t)}
      trailing={
        <button
          type="button"
          onClick={handleOpen}
          aria-label={t("syncSidebar.download.openLabel", { filename })}
          data-testid={`sync-download-open-${download.itemUuid}`}
          className="cursor-pointer rounded-sm text-sm text-blue-600 outline-0 hover:underline focus-visible:outline-2 focus-visible:outline-blue-300"
        >
          {t("syncSidebar.download.open")}
        </button>
      }
    />
  );
});

const designationOf = (
  download: DownloadActivity,
  t: (key: string) => string,
) =>
  download.sourceDesignation
    ? toTitleCase(download.sourceDesignation)
    : t("syncSidebar.unknownSource");
