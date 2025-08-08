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

export type ProxyResponse = ProxyJSONResponse | ProxyStreamResponse;

export type ProxyJSONResponse = {
  error: boolean;
  data: JSONObject;
  status: number;
  headers: Map<string, string>;
};

export type ProxyStreamResponse = {
  sha256sum: string;
};

type JSONPrimitive = string | number | boolean | null;
type JSONArray = JSONValue[];
export interface JSONObject {
  [key: string]: JSONValue;
}

export type JSONValue = JSONPrimitive | JSONArray | JSONObject;

export type ms = number & { readonly __unit: "ms" };

export type Source = {
  uuid: string;
  data: SourceObj;
  isRead: boolean;
  hasAttachment: boolean;
  showMessagePreview: boolean;
  messagePreview: string;
};

export type SourceWithItems = {
  uuid: string;
  data: SourceObj;
  items: Item[];
};

export type SourceObj = {
  fingerprint: string;
  isStarred: boolean;
  journalistDesignation: string;
  lastUpdated: string;
  publicKey: string;
  uuid: string;
};

// Database representation
export type SourceRow = {
  uuid: string;
  data: string; // JSON stringified SourceObj
  is_seen: boolean;
  has_attachment: boolean;
  show_message_preview: boolean;
  message_preview: string;
};

export type Item = {
  uuid: string;
  data: ItemObj;
  plaintext?: string;
  filename?: string;
};

export type ItemObj = {
  uuid: string;
  kind: "message" | "file" | "reply";
  seenBy: string[];
  size: number;
  source: string;
  isRead?: boolean; // only on messages and files
  isDeletedBySource?: boolean; // only on replies
};

// Database representation
export type ItemRow = {
  uuid: string;
  data: string; // JSON stringified ItemObj
  plaintext?: string;
  filename?: string;
};
