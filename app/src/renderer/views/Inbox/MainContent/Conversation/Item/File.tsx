import {
  FetchStatus,
  ItemUpdate,
  ItemUpdateType,
  type Item,
} from "../../../../../../types";
import {
  formatFilename,
  prettyPrintBytes,
  toTitleCase,
} from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import "../Item.css";
import "./File.css";

import { useTranslation } from "react-i18next";
import { File as FileIcon, Download, LoaderCircle, FileX2 } from "lucide-react";
import { Button, Tooltip } from "antd";
import {
  FilePdfFilled,
  FileExcelFilled,
  FileImageFilled,
  FileWordFilled,
  FileZipFilled,
  FilePptFilled,
  FileMarkdownFilled,
  FileFilled,
} from "@ant-design/icons";
import FileVideoFilled from "./FileVideoFilled";
import FileAudioFilled from "./FileAudioFilled";

const EXCEL_EXTENSIONS = new Set([
  ".xls",
  ".xlsx",
  ".xlsm",
  ".xlsb",
  ".xlt",
  ".xltx",
  ".xltm",
  ".csv",
  ".tsv",
  ".ods",
]);

const IMAGE_EXTENSIONS = new Set([
  ".png",
  ".jpg",
  ".jpeg",
  ".gif",
  ".bmp",
  ".tif",
  ".tiff",
  ".svg",
  ".svgz",
  ".webp",
  ".ico",
  ".djvu",
  ".heif",
  ".heic",
  ".avif",
]);

const WORD_EXTENSIONS = new Set([".doc", ".docx", ".rtf", ".odt", ".txt"]);

const ARCHIVE_EXTENSIONS = new Set([
  ".zip",
  ".gz",
  ".tgz",
  ".tar",
  ".bz2",
  ".tbz",
  ".xz",
  ".txz",
  ".7z",
  ".rar",
]);

const POWERPOINT_EXTENSIONS = new Set([
  ".ppt",
  ".pptx",
  ".pps",
  ".ppsx",
  ".odp",
]);

const VIDEO_EXTENSIONS = new Set([
  ".mp4",
  ".mov",
  ".avi",
  ".mkv",
  ".wmv",
  ".flv",
  ".webm",
  ".ogv",
  ".m4v",
  ".mpg",
  ".mpeg",
  ".3gp",
  ".3g2",
]);

const AUDIO_EXTENSIONS = new Set([
  ".mp3",
  ".wav",
  ".flac",
  ".aac",
  ".ogg",
  ".oga",
  ".m4a",
  ".wma",
  ".aif",
  ".aiff",
  ".opus",
]);

interface FileProps {
  item: Item;
  designation: string;
  onUpdate: (update: ItemUpdate) => void;
}

function getFileIconAndColor(filename: string): {
  Icon: React.ComponentType<{
    style?: React.CSSProperties;
    className?: string;
  }>;
  color: string;
} {
  const normalizedFilename = filename.toLowerCase();
  const lastDotIndex = normalizedFilename.lastIndexOf(".");
  const extension =
    lastDotIndex === -1 ? "" : normalizedFilename.substring(lastDotIndex);

  // PDF
  if (extension === ".pdf") {
    return { Icon: FilePdfFilled, color: "#FF4D4F" };
  }

  // Excel
  if (EXCEL_EXTENSIONS.has(extension)) {
    return { Icon: FileExcelFilled, color: "#22B35E" };
  }

  // Image
  if (IMAGE_EXTENSIONS.has(extension)) {
    return { Icon: FileImageFilled, color: "#8C8C8C" };
  }

  // Word
  if (WORD_EXTENSIONS.has(extension)) {
    return { Icon: FileWordFilled, color: "#1677FF" };
  }

  // Zip
  if (ARCHIVE_EXTENSIONS.has(extension)) {
    return { Icon: FileZipFilled, color: "#FAB714" };
  }

  // PowerPoint
  if (POWERPOINT_EXTENSIONS.has(extension)) {
    return { Icon: FilePptFilled, color: "#FF6E31" };
  }

  // Video
  if (VIDEO_EXTENSIONS.has(extension)) {
    return { Icon: FileVideoFilled, color: "#FF4D4F" };
  }

  // Audio
  if (AUDIO_EXTENSIONS.has(extension)) {
    return { Icon: FileAudioFilled, color: "#8C8C8C" };
  }

  // Markdown
  if ([".md", ".markdown"].includes(extension)) {
    return { Icon: FileMarkdownFilled, color: "#8C8C8C" };
  }

  // Other
  return { Icon: FileFilled, color: "#8C8C8C" };
}

function File({ item, designation, onUpdate }: FileProps) {
  const titleCaseDesignation = toTitleCase(designation);
  const fetchStatus = item.fetch_status;

  let fileInner;
  switch (fetchStatus) {
    case FetchStatus.Initial:
      fileInner = InitialFile(item, onUpdate);
      break;
    case FetchStatus.DownloadInProgress:
    case FetchStatus.DecryptionInProgress:
    case FetchStatus.FailedDownloadRetryable:
    case FetchStatus.FailedDecryptionRetryable:
    case FetchStatus.Paused:
      fileInner = InProgressFile(item, onUpdate);
      break;
    case FetchStatus.Complete:
      fileInner = CompleteFile(item);
      break;
    case FetchStatus.FailedTerminal:
      fileInner = FailedFile(item);
      break;
  }

  return (
    <div
      className="flex items-start mb-4 justify-start"
      data-testid={`item-${item.uuid}`}
    >
      <Avatar designation={titleCaseDesignation ?? ""} isActive={false} />
      <div className="ml-3">
        <div className="flex items-center mb-1">
          <span className="author">{titleCaseDesignation ?? ""}</span>
        </div>
        <div className="file-box w-80">{fileInner}</div>
      </div>
    </div>
  );
}

function InitialFile(item: Item, onUpdate: (update: ItemUpdate) => void) {
  const { t } = useTranslation("Item");
  const fileSize = prettyPrintBytes(item.data.size);

  const scheduleDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  return (
    <Tooltip title={t("filenameTooltip")}>
      <div className="flex items-center justify-between pt-2 pb-2">
        <div className="flex items-center">
          <FileIcon size={30} strokeWidth={1} className="file-icon" />
          <div className="ml-2">
            <p className="italic">{t("encryptedFile")}</p>
            <p className="italic">{fileSize}</p>
          </div>
        </div>

        <div className="flex ml-8">
          <Button
            type="text"
            size="large"
            icon={<Download size={20} onClick={scheduleDownload} />}
          />
        </div>
      </div>
    </Tooltip>
  );
}

function InProgressFile(item: Item, onUpdate: (update: ItemUpdate) => void) {
  const { t } = useTranslation("Item");
  const progressBytes = item.fetch_progress ?? 0;
  const fileSize = prettyPrintBytes(item.data.size);
  const progressSize = prettyPrintBytes(progressBytes);
  const progressPct = (progressBytes / item.data.size) * 100;

  const pauseDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.Paused,
    });
  };

  const resumeDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  return (
    <div className="flex items-center justify-start">
      <LoaderCircle
        className={
          item.fetch_status === FetchStatus.DownloadInProgress
            ? "animate-spin file-icon"
            : "file-icon"
        }
        size={30}
        strokeWidth={1}
      />
      <div className="ml-2">
        <p className="italic">{t("encryptedFile")}</p>
        <div className="flex items-center space-x-2 h-3">
          {/* Loading bar */}
          <div className="w-64 h-0.5 bg-gray-200 rounded-full overflow-hidden">
            <div
              className="h-full bg-blue-500 transition-all duration-300 ease-out"
              style={{ width: `${progressPct}%` }}
            ></div>
          </div>
        </div>
        <div className="flex justify-between">
          <p className="italic">
            {progressSize} {t("of")} {fileSize}
          </p>
          {item.fetch_status === FetchStatus.DownloadInProgress ? (
            <Button size="small" type="link" onClick={pauseDownload}>
              {t("pause")}
            </Button>
          ) : (
            <Button size="small" type="link" onClick={resumeDownload}>
              {t("resume")}
            </Button>
          )}
        </div>
      </div>
    </div>
  );
}

// TODO: implement download viewer
function CompleteFile(item: Item) {
  const filename = item.filename
    ? item.filename.substring(item.filename.lastIndexOf("/") + 1)
    : "";
  const fileSize = prettyPrintBytes(item.data.size);

  // Format the filename to cap the length, and show full filename in tooltip if
  // formatted filename is truncated
  const filenameMaxLength = 30;
  const formattedFilename = formatFilename(filename, filenameMaxLength, 6);
  const tooltipTitle = filename.length > filenameMaxLength ? filename : "";

  const { Icon, color } = getFileIconAndColor(filename);

  return (
    <div className="flex items-center justify-start mt-2 mb-2">
      <Icon style={{ fontSize: 30, color }} className="file-icon" />
      <div className="ml-2">
        <Tooltip title={tooltipTitle}>
          <Button size="small" type="link" className="file-namebtn">
            {formattedFilename}
          </Button>
        </Tooltip>

        <p className="italic">{fileSize}</p>
      </div>
    </div>
  );
}

function FailedFile(item: Item) {
  const { t } = useTranslation("Item");
  const fileSize = prettyPrintBytes(item.data.size);

  return (
    <div className="flex items-center justify-between pt-2 pb-2">
      <div className="flex items-center">
        <FileX2 size={30} strokeWidth={1} className="file-icon" />
        <div className="ml-2">
          <p className="italic">{t("encryptedFile")}</p>
          <p className="italic">{fileSize}</p>
        </div>
      </div>
    </div>
  );
}

export default File;
