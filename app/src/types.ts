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

export type Index = {
  sources: {
    [uuid: string]: string;
  };
  items: {
    [uuid: string]: string;
  };
  journalists: {
    [uuid: string]: string;
  };
};

export type BatchRequest = {
  // Metadata requests
  sources: string[];
  items: string[];
  journalists: string[];

  // Pending Events
  events: PendingEvent[];
};

export type BatchResponse = {
  sources: {
    [uuid: string]: SourceMetadata;
  };
  items: {
    [uuid: string]: ItemMetadata;
  };
  journalists: {
    [uuid: string]: JournalistMetadata;
  };
  events: {
    [snowflake_id: string]: number;
  };
};

export type MetadataRequest = {
  sources: string[];
  items: string[];
  journalists: string[];
};

export type MetadataResponse = {
  sources: {
    [uuid: string]: SourceMetadata;
  };
  items: {
    [uuid: string]: ItemMetadata;
  };
  journalists: {
    [uuid: string]: JournalistMetadata;
  };
};

export type SourceMetadata = {
  uuid: string;
  journalist_designation: string;
  is_starred: boolean;
  last_updated: string;
  public_key: string;
  fingerprint: string;
  is_seen: boolean;
};

export type ItemMetadata = ReplyMetadata | SubmissionMetadata;

export type ReplyMetadata = {
  kind: "reply";
  uuid: string;
  source: string;
  size: number;
  journalist_uuid: string;
  is_deleted_by_source: boolean;
  seen_by: string[];
  interaction_count: number;
};

export type SubmissionMetadata = {
  kind: "file" | "message";
  uuid: string;
  source: string;
  size: number;
  is_read: boolean;
  seen_by: string[];
  interaction_count: number;
};

export type JournalistMetadata = {
  uuid: string;
  username: string;
  first_name: string | null;
  last_name: string | null;
};

/** API v1 Types */

export type TokenResponse = {
  expiration: string;
  token: string;
  journalist_uuid: string;
  journalist_first_name: string;
  journalist_last_name: string;
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
  type: number;
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
  Undefined = 0,
  ReplySent = 1,
  ItemDeleted = 2,
  SourceDeleted = 3,
  SourceConversationDeleted = 4,
  Starred = 5,
  Unstarred = 6,
  Seen = 7,
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
  snowflake_id: string;
  type: PendingEventType;
  target: SourceTarget | ItemTarget;
  data?: PendingEventData;
};

export type ReplySentData = {
  text: string;
  metadata: ReplyMetadata;
};

/** Fetch Worker types */
export type FetchDownloadsMessage = {
  authToken: string;
};
