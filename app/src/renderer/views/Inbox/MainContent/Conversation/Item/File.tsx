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

import { useTranslation } from "react-i18next";
import {
  File as FileIcon,
  Download,
  LoaderCircle,
  FileCheck2,
  FileX2,
} from "lucide-react";
import { Button, Tooltip } from "antd";

interface FileProps {
  item: Item;
  designation: string;
  onUpdate: (update: ItemUpdate) => void;
}

function File({ item, designation, onUpdate }: FileProps) {
  const titleCaseDesignation = toTitleCase(designation);
  const fetchStatus = item.fetch_status;

  let fileInner;
  switch (fetchStatus) {
    case FetchStatus.NotScheduled:
      fileInner = NotScheduledFile(item, onUpdate);
      break;
    case FetchStatus.Initial:
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

function NotScheduledFile(item: Item, onUpdate: (update: ItemUpdate) => void) {
  const { t } = useTranslation("Item");
  const fileSize = prettyPrintBytes(item.data.size);

  const scheduleDownload = () => {
    onUpdate({
      item_uuid: item.uuid,
      type: ItemUpdateType.FetchStatus,
      fetch_status: FetchStatus.Initial,
    });
  };

  return (
    <Tooltip title={t("filenameTooltip")}>
      <div className="flex items-center justify-between pt-2 pb-2">
        <div className="flex items-center">
          <FileIcon size={30} strokeWidth={1} style={{ marginRight: 6 }} />
          <div className="ml-2">
            <p style={{ fontStyle: "italic" }}>{t("encryptedFile")}</p>
            <p style={{ fontStyle: "italic" }}>{fileSize}</p>
          </div>
        </div>

        <div className="flex ml-8">
          <Button
            type="text"
            size="large"
            icon={
              <Download
                size={20}
                style={{ verticalAlign: "center" }}
                onClick={scheduleDownload}
              />
            }
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
            ? "animate-spin"
            : ""
        }
        size={30}
        strokeWidth={1}
        style={{ marginRight: 6 }}
      />
      <div className="ml-2">
        <p style={{ fontStyle: "italic" }}>{t("encryptedFile")}</p>
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
          <p style={{ fontStyle: "italic" }}>
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

  return (
    <div className="flex items-center justify-start mt-2 mb-2">
      <FileCheck2
        size={30}
        strokeWidth={1}
        style={{ marginRight: 6, verticalAlign: "center" }}
      />
      <div className="ml-2">
        <Button size="small" type="link" style={{ paddingInlineStart: 0 }}>
          {formatFilename(filename, 30, 6)}
        </Button>
        <p style={{ fontStyle: "italic" }}>{fileSize}</p>
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
        <FileX2 size={30} strokeWidth={1} style={{ marginRight: 6 }} />
        <div className="ml-2">
          <p style={{ fontStyle: "italic" }}>{t("encryptedFile")}</p>
          <p style={{ fontStyle: "italic" }}>{fileSize}</p>
        </div>
      </div>
    </div>
  );
}

export default File;
