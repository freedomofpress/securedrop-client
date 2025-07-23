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
};

export type SourceRow = {
  uuid: string;
  data: string; // JSON stringified SourceObj
};

export type SourceObj = {
  fingerprint: string;
  is_starred: boolean;
  journalist_designation: string;
  last_updated: string;
  public_key: string;
  uuid: string;
};

export type Item = {
  uuid: string;
  data: ItemObj;
  plaintext?: string;
  filename?: string;
};

export type ItemRow = {
  uuid: string;
  data: string; // JSON stringified ItemObj
  plaintext?: string;
  filename?: string;
};

export type ItemObj = {
  is_read: boolean;
  kind: string;
  seen_by: string[];
  size: number;
  source: string;
  uuid: string;
};
