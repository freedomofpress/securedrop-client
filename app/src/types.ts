export type ProxyRequest = {
  method: "GET" | "POST" | "DELETE";
  path_query: string;
  stream: false;
  body?: string;
  headers: object;
};

export type ProxyResponse = {
  data: JSONObject;
  status: number;
  headers: Map<string, string>;
};

type JSONPrimitive = string | number | boolean | null;
type JSONArray = JSONValue[];
export interface JSONObject {
  [key: string]: JSONValue;
}
export type JSONValue = JSONPrimitive | JSONArray | JSONObject;
