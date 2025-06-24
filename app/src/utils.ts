// Temporary function to have something to test
export function sum(a: number, b: number): number {
  return a + b;
}

type JSONPrimitive = string | number | boolean | null;
type JSONArray = JSONValue[];
export interface JSONObject {
  [key: string]: JSONValue;
}
export type JSONValue = JSONPrimitive | JSONArray | JSONObject;
