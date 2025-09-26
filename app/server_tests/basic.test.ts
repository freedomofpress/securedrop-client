import { describe, expect, inject, it } from "vitest";

import { proxyJSONRequest } from "../src/main/proxy";

describe("Test login via setup.ts worked", async () => {
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("logged in as journalist", async () => {
    const result = await proxyJSONRequest({
      method: "GET",
      path_query: "/api/v1/user",
      headers: { Authorization: inject("authHeader") },
    });
    expect(result.status).toEqual(200);
    expect(result.headers.get("content-type")).toEqual("application/json");
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    expect((result.data as any).username).toEqual("journalist");
    // UUID matches what we set in data.yaml
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    expect((result.data as any).uuid).toEqual(
      "be726875-1290-49d4-922d-2fc0901c9266",
    );
  });
});
