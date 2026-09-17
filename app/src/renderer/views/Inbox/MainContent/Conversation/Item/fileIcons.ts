import type { ComponentType, CSSProperties } from "react";

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

export type FileIcon = ComponentType<{
  style?: CSSProperties;
  className?: string;
}>;

// Map a filename's extension onto the icon and brand colour used to represent
// that file type across the app.
export function getFileIconAndColor(filename: string): {
  Icon: FileIcon;
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
