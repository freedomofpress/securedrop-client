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
