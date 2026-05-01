// Branded string that carries the element type at compile time.
// At runtime this is a plain string, so better-sqlite3 sees no difference.
export type JsonArray<T> = string & { readonly __jsonArray: T[] };

export function jsonArray<T>(values: T[]): JsonArray<T> {
  return JSON.stringify(values) as JsonArray<T>;
}
