export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream?: boolean;
  body?: string;
  headers: Record<string, string>;
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
} from "./schemas";

export type {
  TokenResponse,
  Index,
  BatchResponse,
  SourceMetadata,
  ItemMetadata,
  ReplyMetadata,
  SubmissionMetadata,
  JournalistMetadata,
};

export type BatchRequest = {
  // Metadata requests
  sources: string[];
  items: string[];
  journalists: string[];

  // Pending Events
  events: PendingEvent[];
};

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
  showMessagePreview: boolean;
  messagePreview: string;
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
  show_message_preview: boolean;
  message_preview: string;
};

export type Item = {
  uuid: string;
  data: ItemMetadata;
  plaintext?: string;
  filename?: string;
  fetch_status?: FetchStatus;
  fetch_progress?: number;
};

// Database representation
export type ItemRow = {
  uuid: string;
  data: string; // JSON stringified ItemMetadata
  plaintext?: string;
  filename?: string;
  fetch_status: number; // FetchStatus enum
  fetch_progress: number;
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

export enum PendingEventType {
  Undefined = "undefined",
  ReplySent = "reply_sent",
  ItemDeleted = "item_deleted",
  SourceDeleted = "source_deleted",
  SourceConversationDeleted = "source_conversation_deleted",
  Starred = "source_starred",
  Unstarred = "source_unstarred",
  Seen = "item_seen",
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

export type SourceTarget = {
  source_uuid: string;
  version: string;
};

export type ItemTarget = {
  item_uuid: string;
  version: string;
};

export type PendingEvent = {
  id: string;
  type: PendingEventType;
  target: SourceTarget | ItemTarget;
  data?: PendingEventData;
};

export type ReplySentData = {
  uuid: string;
  // reply ciphertext
  reply: string;
  // reply plaintext: for storing in pending_events table only
  plaintext: string;
  metadata: ReplyMetadata;
};

/** Fetch Worker types */
export type FetchDownloadsMessage = {
  authToken: string;
};
