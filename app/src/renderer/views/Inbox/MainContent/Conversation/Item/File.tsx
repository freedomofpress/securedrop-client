import { memo, useState, useEffect } from "react";
import {
  FetchStatus,
  ItemUpdate,
  ItemUpdateType,
  type ExportPayload,
  type PrintPayload,
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
import {
  File as FileIcon,
  Download,
  LoaderCircle,
  LockKeyhole,
  Trash,
} from "lucide-react";
import { Button, Tooltip, theme, Dropdown } from "antd";
import type { MenuProps } from "antd";
import {
  FilePdfFilled,
  FileExcelFilled,
  FileImageFilled,
  FileWordFilled,
  FileZipFilled,
  FilePptFilled,
  FileMarkdownFilled,
  FileFilled,
  ExclamationCircleTwoTone,
  MoreOutlined,
} from "@ant-design/icons";
import FileVideoFilled from "./FileVideoFilled";
import FileAudioFilled from "./FileAudioFilled";
import { ExportWizard } from "./Export";
import { PrintWizard } from "./Print";
import { useAppSelector } from "../../../../../hooks";
import {
  getSessionState,
  SessionStatus,
} from "../../../../../features/session/sessionSlice";

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
  ".jxl",
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
  onDelete: () => void;
  positionInConversation?: number;
  totalConversationItems?: number;
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

const File = memo(function File({
  item,
  designation,
  onUpdate,
  onDelete,
  positionInConversation,
  totalConversationItems,
}: FileProps) {
  const { t } = useTranslation("Item");
  const { token } = theme.useToken();
  const titleCaseDesignation = toTitleCase(designation);
  const fetchStatus = item.fetch_status;
  const [isFileBoxHovered, setIsFileBoxHovered] = useState(false);
  const [isDeleteFocused, setIsDeleteFocused] = useState(false);
  const showDelete = isFileBoxHovered || isDeleteFocused;

  // Disable downloading of files in offline mode
  const session = useAppSelector(getSessionState);
  const disableFetch = session.status !== SessionStatus.Auth;

  const isClickable =
    !disableFetch &&
    (fetchStatus === FetchStatus.Initial ||
      fetchStatus === FetchStatus.Cancelled);

  const isInitialState =
    fetchStatus === FetchStatus.Initial ||
    fetchStatus === FetchStatus.Cancelled;

  let FileInner;
  switch (fetchStatus) {
    case FetchStatus.Initial:
    case FetchStatus.Cancelled:
      FileInner = InitialFile;
      break;
    case FetchStatus.DownloadInProgress:
    case FetchStatus.DecryptionInProgress:
    case FetchStatus.FailedDownloadRetryable:
    case FetchStatus.FailedDecryptionRetryable:
    case FetchStatus.Paused:
    case FetchStatus.ScheduledDeletion:
      FileInner = InProgressFile;
      break;
    case FetchStatus.Complete:
      FileInner = CompleteFile;
      break;
    case FetchStatus.FailedTerminal:
      FileInner = FailedFile;
      break;
    default:
      throw new Error(`Unknown fetch status: ${fetchStatus}`);
  }

  const handleClick = () => {
    if (disableFetch) {
      return;
    }
    if (
      fetchStatus === FetchStatus.Initial ||
      fetchStatus === FetchStatus.Cancelled
    ) {
      onUpdate({
        item_uuid: item.uuid,
        type: ItemUpdateType.FetchStatus,
        fetch_status: FetchStatus.DownloadInProgress,
      });
    }
  };

  // Apply error border color using theme token when in failed state
  // Apply hover background color for initial state (or cancelled)
  const fileBoxStyle = {
    ...(fetchStatus === FetchStatus.FailedTerminal
      ? { borderColor: token.colorErrorBorder }
      : undefined),
    ...((fetchStatus === FetchStatus.Initial ||
      fetchStatus === FetchStatus.Cancelled) &&
    isFileBoxHovered
      ? { backgroundColor: token.colorFillQuaternary }
      : undefined),
    ...(isClickable ? { cursor: "pointer" } : undefined),
    transition: "background-color 0.2s ease",
  };

  const listItemAriaProps =
    positionInConversation && totalConversationItems
      ? {
          role: "listitem" as const,
          "aria-posinset": positionInConversation,
          "aria-setsize": totalConversationItems,
          "aria-label": t("filePositionAriaLabel", {
            index: positionInConversation,
            total: totalConversationItems,
          }),
        }
      : {};

  return (
    <div
      className="flex items-start mb-4 justify-start group"
      data-testid={`item-${item.uuid}`}
      {...listItemAriaProps}
    >
      <Avatar designation={titleCaseDesignation ?? ""} isActive={false} />
      <div className="ml-3">
        <div className="flex items-center mb-1">
          <span className="author">{titleCaseDesignation ?? ""}</span>
        </div>
        <div className="flex items-center gap-1">
          <Tooltip
            title={
              isInitialState
                ? disableFetch
                  ? t("offlineFilenameTooltip")
                  : t("filenameTooltip")
                : undefined
            }
            trigger={["hover", "focus"]}
          >
            <div
              role="button"
              tabIndex={isClickable || isInitialState ? 0 : undefined}
              className="w-80 file-box"
              style={fileBoxStyle}
              onClick={handleClick}
              onKeyDown={(e) => {
                if (
                  e.target === e.currentTarget &&
                  (e.key === "Enter" || e.key === " ")
                ) {
                  e.preventDefault();
                  handleClick();
                }
              }}
              onMouseEnter={() => setIsFileBoxHovered(true)}
              onMouseLeave={() => setIsFileBoxHovered(false)}
            >
              <FileInner
                disableFetch={disableFetch}
                item={item}
                onUpdate={onUpdate}
                onDelete={onDelete}
              />
            </div>
          </Tooltip>
          {!disableFetch && (
            <div
              className="flex-shrink-0 transition-opacity group-hover:opacity-100"
              style={{ opacity: showDelete ? 1 : 0 }}
            >
              <Button
                type="text"
                size="small"
                danger
                icon={<Trash size={16} />}
                onClick={onDelete}
                aria-label={t("deleteFile")}
                onFocus={() => setIsDeleteFocused(true)}
                onBlur={() => setIsDeleteFocused(false)}
                data-testid="file-delete-button"
              />
            </div>
          )}
        </div>
      </div>
    </div>
  );
});

interface FileViewProps {
  item: Item;
  onUpdate: (update: ItemUpdate) => void;
  disableFetch: boolean;
  onDelete?: () => void;
}

const InitialFile = memo(function InitialFile({
  item,
  onUpdate,
  disableFetch,
}: FileViewProps) {
  const { t } = useTranslation("Item");
  const fileSize = prettyPrintBytes(item.data.size);

  const scheduleDownload = (e: React.MouseEvent) => {
    e.stopPropagation();
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  return (
    <div className="flex items-center justify-between pt-2 pb-2">
      <div className="flex items-center">
        <FileIcon
          size={30}
          strokeWidth={1}
          className="file-icon"
          aria-hidden="true"
        />
        <div className="ml-2">
          <p className="italic">{t("encryptedFile")}</p>
          <p className="italic">{fileSize}</p>
        </div>
      </div>

      <div className="flex ml-8">
        <Button
          type="text"
          size="large"
          icon={<Download size={20} />}
          onClick={scheduleDownload}
          disabled={disableFetch}
          aria-label={t("downloadFile")}
        />
      </div>
    </div>
  );
});

const InProgressFile = memo(function InProgressFile({
  item,
  onUpdate,
  disableFetch,
}: FileViewProps) {
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

  const cancelDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.Cancelled,
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
          <div className="flex gap-1">
            {item.fetch_status === FetchStatus.DownloadInProgress ? (
              <Button
                size="small"
                type="link"
                onClick={pauseDownload}
                disabled={disableFetch}
              >
                {t("pause")}
              </Button>
            ) : (
              <Button
                size="small"
                type="link"
                onClick={resumeDownload}
                disabled={disableFetch}
              >
                {t("resume")}
              </Button>
            )}
            <Button
              size="small"
              type="link"
              onClick={cancelDownload}
              disabled={disableFetch}
            >
              {t("cancel")}
            </Button>
          </div>
        </div>
      </div>
    </div>
  );
});

const CompleteFile = memo(function CompleteFile({
  item,
  onDelete,
  disableFetch,
}: {
  item: Item;
  onDelete?: () => void;
  disableFetch: boolean;
}) {
  const { t } = useTranslation("Item");
  const [whistleflowEnabled, setWhistleflowEnabled] = useState(false);
  const [exportWizardOpen, setExportWizardOpen] = useState(false);
  const [exportWizardKey, setExportWizardKey] = useState(0);
  const [exportWhistleflow, setExportWhistleflow] = useState(false);
  const [printWizardOpen, setPrintWizardOpen] = useState(false);

  useEffect(() => {
    window.electronAPI.getWhistleflowEnabled().then(setWhistleflowEnabled);
  }, []);

  const filename = item.filename
    ? item.filename.substring(item.filename.lastIndexOf("/") + 1)
    : "";
  // Use decrypted_size if available (after download), otherwise fall back to server-reported size
  const fileSize = prettyPrintBytes(item.decrypted_size ?? item.data.size);

  const exportPayload: ExportPayload = {
    type: "file",
    payload: item,
  };

  const printPayload: PrintPayload = {
    type: "file",
    payload: item,
  };

  // Format the filename to cap the length, and show full filename in tooltip if
  // formatted filename is truncated
  const filenameMaxLength = 30;
  const formattedFilename = formatFilename(filename, filenameMaxLength, 6);
  const tooltipTitle = filename.length > filenameMaxLength ? filename : "";

  const { Icon, color } = getFileIconAndColor(filename);

  const handleOpenFile = async () => {
    try {
      await window.electronAPI.openFile(item.uuid);
    } catch (error) {
      console.error("Failed to open file:", error);
    }
  };

  const handleExportClick = () => {
    setExportWhistleflow(false);
    setExportWizardKey((k) => k + 1);
    setExportWizardOpen(true);
  };

  const handleExportToWhistleflowClick = () => {
    setExportWhistleflow(true);
    setExportWizardKey((k) => k + 1);
    setExportWizardOpen(true);
  };

  const handlePrintClick = () => {
    setPrintWizardOpen(true);
  };

  const handleExportWizardClose = () => {
    setExportWizardOpen(false);
    // Note: ExportWizard handles state cleanup via its useEffect when open changes
  };

  const handlePrintWizardClose = () => {
    setPrintWizardOpen(false);
    // Note: PrintWizard handles state cleanup via its useEffect when open changes
  };

  const menuItems: MenuProps["items"] = [
    {
      key: "view",
      label: t("viewFile"),
      onClick: handleOpenFile,
    },
    {
      key: "export",
      label: t("exportToUSB"),
      onClick: handleExportClick,
    },
    ...(whistleflowEnabled
      ? [
          {
            key: "exportToWhistleflow",
            label: t("exportToWhistleflow"),
            onClick: handleExportToWhistleflowClick,
          },
        ]
      : []),
    {
      key: "print",
      label: t("printFile"),
      onClick: handlePrintClick,
    },
    ...(onDelete && !disableFetch
      ? [
          { type: "divider" as const },
          {
            key: "delete",
            label: t("deleteFile"),
            danger: true,
            onClick: onDelete,
          },
        ]
      : []),
  ];

  return (
    <>
      <div className="flex items-center justify-between mt-2 mb-2">
        <div className="flex items-center">
          <Icon style={{ fontSize: 30, color }} className="file-icon" />
          <div className="ml-2">
            <Tooltip title={tooltipTitle} trigger={["hover", "focus"]}>
              <Button
                size="small"
                type="link"
                className="file-namebtn"
                onClick={handleOpenFile}
                aria-label={filename}
              >
                {formattedFilename}
              </Button>
            </Tooltip>

            <p className="italic">{fileSize}</p>
          </div>
        </div>

        <div className="flex gap-1">
          <Dropdown
            menu={{ items: menuItems }}
            placement="bottomRight"
            trigger={["click"]}
          >
            <Button
              type="text"
              size="small"
              icon={<MoreOutlined style={{ fontSize: 18 }} />}
              aria-label={t("fileActions")}
            />
          </Dropdown>
        </div>
      </div>

      {item.isDoubleEncrypted && (
        <Tooltip title={t("doubleEncryptedTooltip")}>
          <span className="double-encrypted-badge">
            <LockKeyhole size={12} /> {t("doubleEncryptedBadge")}
          </span>
        </Tooltip>
      )}
      <ExportWizard
        key={exportWizardKey}
        item={exportPayload}
        open={exportWizardOpen}
        onClose={handleExportWizardClose}
        whistleflow={exportWhistleflow}
      />
      <PrintWizard
        item={printPayload}
        open={printWizardOpen}
        onClose={handlePrintWizardClose}
      />
    </>
  );
});

const FailedFile = memo(function FailedFile({
  item,
  onUpdate,
  disableFetch,
}: FileViewProps) {
  const { t } = useTranslation("Item");
  const { token } = theme.useToken();

  const retryDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.DownloadInProgress,
    });
  };

  const cancelDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.Cancelled,
    });
  };

  return (
    <div className="flex items-center justify-between pt-2 pb-2">
      <div className="flex items-center">
        <ExclamationCircleTwoTone
          twoToneColor={token.colorError}
          style={{ fontSize: 30 }}
        />
        <div className="ml-2">
          <p className="italic">{t("encryptedFile")}</p>
          <p className="text-gray-700">{t("downloadFailed")}</p>
        </div>
      </div>
      <div className="flex gap-2">
        <Button
          type="link"
          size="small"
          onClick={retryDownload}
          disabled={disableFetch}
        >
          {t("retry")}
        </Button>
        <Button
          type="link"
          size="small"
          onClick={cancelDownload}
          disabled={disableFetch}
        >
          {t("cancel")}
        </Button>
      </div>
    </div>
  );
});

export default File;
