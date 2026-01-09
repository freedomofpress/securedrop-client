export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream?: boolean;
  body?: string;
  headers: Record<string, string>;
  timeout?: number;
};

export type ProxyCommand = {
  command: string;
  options: string[];
  env: Map<string, string>;
  timeout: ms;
  abortSignal?: AbortSignal;
};

export type ProxyResponse = ProxyJSONResponse | ProxyStreamResponse;

export type ProxyJSONResponse = {
  error: boolean;
  data?: JSONValue;
  status: number;
  headers: Map<string, string>;
};

export type ProxyStreamResponse = {
  bytesWritten: number;
  complete: boolean;
  error?: Error;
  sha256sum?: string;
};

type JSONPrimitive = string | number | boolean | null;
type JSONArray = JSONValue[];
export type JSONObject = {
  [key: string]: JSONValue;
};

export type JSONValue = JSONPrimitive | JSONArray | JSONObject;

export type ms = number & { readonly __unit: "ms" };

/** Sync types */

export enum SyncStatus {
  NOT_MODIFIED = "not_modified",
  UPDATED = "updated",
  ERROR = "error",
  FORBIDDEN = "forbidden",
}

// IPC request for operation requiring auth token
// ex: syncMetadata, fetchDownloads
export type AuthedRequest = {
  authToken: string;
};

// Re-export some types that are derived from zod schemas
import type {
  TokenResponse,
  Index,
  BatchResponse,
  SourceMetadata,
  ItemMetadata,
  ReplyMetadata,
  SubmissionMetadata,
  JournalistMetadata,
  BatchRequest,
  SourceTarget,
  ItemTarget,
  PendingEvent,
} from "./schemas";
import { PendingEventType } from "./schemas";

export type {
  TokenResponse,
  Index,
  BatchResponse,
  SourceMetadata,
  ItemMetadata,
  ReplyMetadata,
  SubmissionMetadata,
  JournalistMetadata,
  BatchRequest,
  SourceTarget,
  ItemTarget,
  PendingEvent,
};

export { PendingEventType };

export type MetadataRequest = {
  sources: string[];
  items: string[];
  journalists: string[];
};

/** UI Types */

export type Source = {
  uuid: string;
  data: SourceMetadata;
  isRead: boolean;
  hasAttachment: boolean;
  messagePreview: MessagePreview | null;
};

export type MessagePreview = {
  kind: "message" | "reply" | "file";
  plaintext: string | null;
};

export type SourceWithItems = {
  uuid: string;
  data: SourceMetadata;
  items: Item[];
};

export type Journalist = {
  uuid: string;
  data: JournalistMetadata;
};

// Defines an item update in the UI, to be translated
// to write events dispatched to the main process
export type ItemUpdate = {
  item_uuid: string;
  type: ItemUpdateType;
  fetch_status?: number;
  // TODO: define other item updates
};

export enum ItemUpdateType {
  FetchStatus = 1,
}

// Database representation
export type SourceRow = {
  uuid: string;
  data: string; // JSON stringified SourceMetadata
  is_seen: boolean;
  has_attachment: boolean;
  last_message_kind?: "message" | "reply" | "file";
  last_message_plaintext?: string;
  last_message_filename?: string;
};

export type Item = {
  uuid: string;
  data: ItemMetadata;
  plaintext?: string;
  filename?: string;
  fetch_status?: FetchStatus;
  fetch_progress?: number;
  decrypted_size?: number;
};

// Database representation
export type ItemRow = {
  uuid: string;
  data: string; // JSON stringified ItemMetadata
  plaintext?: string;
  filename?: string;
  fetch_status: number; // FetchStatus enum
  fetch_progress: number;
  decrypted_size?: number;
};

// Database representation
export type JournalistRow = {
  uuid: string;
  data: string; // JSON stringified JournalistMetadata
  version: string;
};

export type PendingEventRow = {
  snowflake_id: string;
  source_uuid: string;
  item_uuid: string;
  type: string;
  data: string; // JSON stringified PendingEventData
};

export enum FetchStatus {
  Initial = 0,
  DownloadInProgress = 1,
  DecryptionInProgress = 2,
  Complete = 3,
  Paused = 4,
  // Download failed, but will retry
  FailedDownloadRetryable = 5,
  // Decryption failed, but will retry
  FailedDecryptionRetryable = 6,
  // Exceeded max retries, considered terminally failed
  FailedTerminal = 7,
}

// EventStatus codes returned from the server
export enum EventStatus {
  Processing = 102,
  OK = 200,
  AlreadyReported = 208,
  BadRequest = 400,
  NotFound = 404,
  NotImplemented = 501,
}

export type PendingEventData = ReplySentData;

export type ReplySentData = {
  uuid: string;
  // reply ciphertext
  reply: string;

  // fields for storing in pending_events table only: not
  // to be sent to the server + excluded from the request schema
  plaintext: string;
  metadata: ReplyMetadata;
};

/** Fetch Worker types */
export type FetchDownloadsMessage = {
  authToken: string;
};

/** Print + Export types */

// All possible strings returned by the qrexec calls to sd-devices. These values come from
// `print/status.py` and `disk/status.py` in `securedrop-export`
// and must only be changed in coordination with changes released in that component.
export type DeviceStatus =
  | ExportStatus
  | PrintStatus
  | DeviceErrorStatus
  | ArchiveStatus;

export enum DeviceErrorStatus {
  // Misc errors
  CALLED_PROCESS_ERROR = "CALLED_PROCESS_ERROR",
  ERROR_USB_CONFIGURATION = "ERROR_USB_CONFIGURATION",
  UNEXPECTED_RETURN_STATUS = "UNEXPECTED_RETURN_STATUS",

  // Client-side error only
  ERROR_MISSING_FILES = "ERROR_MISSING_FILES", // All files meant for export are missing
}

export enum ExportStatus {
  // Success
  SUCCESS_EXPORT = "SUCCESS_EXPORT",

  // Error
  NO_DEVICE_DETECTED = "NO_DEVICE_DETECTED",
  INVALID_DEVICE_DETECTED = "INVALID_DEVICE_DETECTED", // Multi partitioned, not encrypted, etc
  MULTI_DEVICE_DETECTED = "MULTI_DEVICE_DETECTED", // Not currently supported
  UNKNOWN_DEVICE_DETECTED = "UNKNOWN_DEVICE_DETECTED", // Badly-formatted USB or VeraCrypt/TC

  DEVICE_LOCKED = "DEVICE_LOCKED", // One valid device detected, and it's locked
  DEVICE_WRITABLE = "DEVICE_WRITABLE", // One valid device detected, and it's unlocked (and mounted)

  ERROR_UNLOCK_LUKS = "ERROR_UNLOCK_LUKS",
  ERROR_UNLOCK_GENERIC = "ERROR_UNLOCK_GENERIC",
  ERROR_MOUNT = "ERROR_MOUNT", // Unlocked but not mounted

  ERROR_EXPORT = "ERROR_EXPORT", // Could not write to disk

  // Export succeeds but drives were not properly closed
  ERROR_EXPORT_CLEANUP = "ERROR_EXPORT_CLEANUP",
  ERROR_UNMOUNT_VOLUME_BUSY = "ERROR_UNMOUNT_VOLUME_BUSY",

  DEVICE_ERROR = "DEVICE_ERROR", // Something went wrong while trying to check the device
}

export enum PrintStatus {
  // Success
  PRINT_PREFLIGHT_SUCCESS = "PRINTER_PREFLIGHT_SUCCESS",
  TEST_SUCCESS = "PRINTER_TEST_SUCCESS",
  PRINT_SUCCESS = "PRINTER_SUCCESS",

  // Error
  ERROR_PRINTER_NOT_FOUND = "ERROR_PRINTER_NOT_FOUND",
  ERROR_PRINT = "ERROR_PRINT",
  ERROR_UNPRINTABLE_TYPE = "ERROR_UNPRINTABLE_TYPE",
  ERROR_MIMETYPE_UNSUPPORTED = "ERROR_MIMETYPE_UNSUPPORTED",
  ERROR_MIMETYPE_DISCOVERY = "ERROR_MIMETYPE_DISCOVERY",
  ERROR_UNKNOWN = "ERROR_GENERIC", // Unknown printer error, backwards-compatible
}

export enum ArchiveStatus {
  ERROR_ARCHIVE_METADATA = "ERROR_ARCHIVE_METADATA",
  ERROR_METADATA_PARSING = "ERROR_METADATA_PARSING",
  ERROR_EXTRACTION = "ERROR_EXTRACTION",
}
