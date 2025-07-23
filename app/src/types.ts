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

export interface Index {
  sources: IndexSourceVersions;
}

export interface IndexSourceVersions {
  [uuid: string]: SourceVersion;
}

export interface SourceVersion {
  version: string;
  collection: ItemVersions;
}

export interface ItemVersions {
  // UUID: version for each item in the source
  [uuid: string]: string;
}

export interface SyncMetadataRequest {
  authToken: string;
}

export interface SourceSyncRequest {
  full_sources: string[];
  partial_sources: {
    // source_uuid: [item_uuid, ...]
    [uuid: string]: string[];
  };
}

export interface SourceMetadata {
  info: {
    uuid: string;
    journalist_designation: string;
    is_starred: boolean;
    last_updated: string;
    public_key: string;
    fingerprint: string;
  };
  collection: {
    [uuid: string]: string;
  };
}

export interface SourceSyncResponse {
  sources: {
    [sourceUUID: string]: SourceMetadata;
  };
}
