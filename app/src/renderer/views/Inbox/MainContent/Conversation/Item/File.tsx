import { FetchStatus, type Item } from "../../../../../../types";
import { prettyPrintBytes, toTitleCase } from "../../../../../utils";
import Avatar from "../../../../../components/Avatar";
import "../Item.css";

import { useTranslation } from "react-i18next";
import {
  File as FileIcon,
  Download,
  LoaderCircle,
  FileCheck2,
} from "lucide-react";
import { Button } from "antd";

interface FileProps {
  item: Item;
  designation: string;
}

function File({ item, designation }: FileProps) {
  const titleCaseDesignation = toTitleCase(designation);

  const fetchStatus = item.fetch_status;

  let fileInner = InitialFile(item);
  switch (fetchStatus) {
    case FetchStatus.Initial:
      fileInner = InitialFile(item);
      break;
    case FetchStatus.DownloadInProgress:
    case FetchStatus.DecryptionInProgress:
    case FetchStatus.FailedDownloadRetryable:
    case FetchStatus.FailedDecryptionRetryable:
      fileInner = InProgressFile(item);
      break;
    case FetchStatus.Complete:
      fileInner = CompleteFile(item);
      break;
    case FetchStatus.Paused:
      // TODO: design + implement paused file download
      break;
    case FetchStatus.FailedTerminal:
      // TODO: design + implement terminally failed file download
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

function InitialFile(item: Item) {
  const { t } = useTranslation("Item");
  const fileSize = prettyPrintBytes(item.data.size);

  // TODO(vicki): add tooltip
  // TODO(vicki): hook up button
  return (
    <div className="flex items-center justify-between mt-2 mb-2">
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
          icon={<Download size={20} style={{ verticalAlign: "center" }} />}
        />
      </div>
    </div>
  );
}

function InProgressFile(item: Item) {
  const { t } = useTranslation("Item");
  const progressBytes = item.fetch_progress ?? 0;
  const fileSize = prettyPrintBytes(item.data.size);
  const progressSize = prettyPrintBytes(progressBytes);
  const progressPct = (progressBytes / item.data.size) * 100;

  // TODO(vicki): hook up cancel button
  // TODO(vicki): verify that progress incrementally updates with hook from item??
  return (
    <div className="flex items-center justify-start">
      <LoaderCircle
        className="animate-spin"
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
          <Button size="small" type="link">
            {t("cancel")}
          </Button>
        </div>
      </div>
    </div>
  );
}

// TODO: file link opens download viewer
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
          {filename}
        </Button>
        <p style={{ fontStyle: "italic" }}>{fileSize}</p>
      </div>
    </div>
  );
}

export default File;
