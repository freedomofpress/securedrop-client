export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream: boolean;
  body?: string;
  headers: object;
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
  sha256sum: string;
};

type JSONPrimitive = string | number | boolean | null;
type JSONArray = JSONValue[];
export type JSONObject = {
  [key: string]: JSONValue;
};

export type JSONValue = JSONPrimitive | JSONArray | JSONObject;

export type ms = number & { readonly __unit: "ms" };

/** Sync types */

// IPC request for syncMetadata operation
export type SyncMetadataRequest = {
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
};

export type SubmissionMetadata = {
  kind: "file" | "message";
  uuid: string;
  source: string;
  size: number;
  is_read: boolean;
  seen_by: string[];
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
};

// Database representation
export type ItemRow = {
  uuid: string;
  data: string; // JSON stringified ItemMetadata
  plaintext?: string;
  filename?: string;
};

// Database representation
export type JournalistRow = {
  uuid: string;
  data: string; // JSON stringified JournalistMetadata
  version: string;
};
