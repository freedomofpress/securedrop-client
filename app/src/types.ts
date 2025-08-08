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
  proxyOrigin: string;
  timeout: ms;
  abortSignal?: AbortSignal;
};

export type ProxyResponse<T> = ProxyJSONResponse<T> | ProxyStreamResponse;

export type ProxyJSONResponse<T> = {
  error: boolean;
  data?: T;
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
export interface SyncMetadataRequest {
  authToken: string;
}

export interface Index {
  sources: {
    [uuid: string]: string;
  };
  items: {
    [uuid: string]: string;
  };
}

export interface MetadataRequest {
  sources: string[];
  items: string[];
}

export interface MetadataResponse {
  sources: {
    [uuid: string]: SourceMetadata;
  };
  items: {
    [uuid: string]: ItemMetadata;
  };
}

export interface SourceMetadata {
  uuid: string;
  journalist_designation: string;
  is_starred: boolean;
  last_updated: string;
  public_key: string;
  fingerprint: string;
}

export type ItemMetadata = ReplyMetadata | SubmissionMetadata;

export interface ReplyMetadata {
  kind: "reply";
  uuid: string;
  source: string;
  size: number;
  journalist_uuid: string;
  is_deleted_by_source: boolean;
  seen_by: string[];
}

export interface SubmissionMetadata {
  kind: "file" | "message";
  uuid: string;
  source: string;
  size: number;
  is_read: boolean;
  seen_by: string[];
}

/** API v1 Types */

export interface TokenResponse {
  expiration: string;
  token: string;
  journalist_uuid: string;
  journalist_first_name: string;
  journalist_last_name: string;
}
