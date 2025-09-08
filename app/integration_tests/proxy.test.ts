import { describe, expect, it } from "vitest";

import { PassThrough } from "node:stream";

import { proxyJSONRequest, proxyStreamRequest } from "../src/main/proxy";
import { JSONObject, ProxyCommand, ProxyJSONResponse, ms } from "../src/types";

vi.mock("../src/main/proxy", async () => {
  const actual = await vi.importActual("../src/main/proxy");
  return {
    ...actual,
    buildProxyCommand: vi.fn(mockProxyCommand),
  };
});

const mockProxyCommand = vi.hoisted(() => (): ProxyCommand => {
  return {
    command: sdProxyCommand,
    options: [],
    env: new Map([
      ["SD_PROXY_ORIGIN", sdProxyOrigin],
      ["DISABLE_TOR", "yes"],
    ]),
    timeout: 1000 as ms,
  };
});

describe("Test executing JSON proxy commands against httpbin", async () => {
  it("successful JSON response", async () => {
    const result = await proxyJSONRequest({
      method: "GET",
      path_query: "/json",
      headers: {},
    });
    expect(result.status).toEqual(200);
    expect(result.headers.get("content-type")).toEqual("application/json");
  });

  it.for([200, 204, 404])(
    "2xx and 404 HTTP codes are passed through cleanly",
    async (statusCode: number) => {
      const result = await proxyJSONRequest({
        method: "GET",
        path_query: `/status/${statusCode}`,
        headers: {},
      });

      expect(result.status).toEqual(statusCode);
    },
  );

  it.for([401, 403, 429])(
    "4xx HTTP codes returns error: true response",
    async (statusCode: number) => {
      const result = await proxyJSONRequest({
        method: "GET",
        path_query: `/status/${statusCode}`,
        headers: {},
      });
      expect(result.error);
      expect(result.status).toEqual(statusCode);
    },
  );

  it.for([500, 503, 504])(
    "5xx HTTP codes returns error: true response",
    async (statusCode: number) => {
      const result = await proxyJSONRequest({
        method: "GET",
        path_query: `/status/${statusCode}`,
        headers: {},
      });
      expect(result.error);
      expect(result.status).toEqual(statusCode);
    },
  );

  it("path query with query parameters", async () => {
    const result = await proxyJSONRequest({
      method: "GET",
      path_query: "/get?foo=bar",
      headers: {},
    });
    expect(result.status).toEqual(200);
    expect((result.data! as JSONObject)["args"]).toEqual({ foo: "bar" });
  });

  it("proxy subcommand terminates with SIGTERM on timeout", async () => {
    await expect(
      proxyJSONRequest({
        method: "GET",
        path_query: "/delay/10",
        headers: {},
      }),
    ).rejects.toThrowError("Process terminated with signal SIGTERM");
  });

  it("proxy subcommand aborts", async () => {
    const abortController = new AbortController();

    const proxyExec = proxyJSONRequest(
      {
        method: "GET",
        path_query: "/delay/100",
        headers: {},
      },
      abortController.signal,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });

  it("request with headers", async () => {
    const result = await proxyJSONRequest({
      method: "GET",
      path_query: "/headers",
      headers: { "X-Test-Header": "th" },
    });
    expect(result.status).toEqual(200);
    expect((result.data! as JSONObject)["headers"]).toHaveProperty(
      "X-Test-Header",
      "th",
    );
  });

  it("request with body", async () => {
    const input = { id: 42, title: "test" };
    const result = await proxyJSONRequest({
      method: "POST",
      path_query: "/post",
      body: JSON.stringify(input),
      headers: {},
    });
    expect(result.status).toEqual(200);
    expect((result.data! as JSONObject)["json"]).toEqual(input);
  });
});

describe("Test executing streaming proxy", async () => {
  it("proxy successfully streams data", async () => {
    const writeStream = new PassThrough();
    let streamData = "";
    writeStream.on("data", (chunk) => {
      streamData += chunk;
    });

    const count = 20;
    await proxyStreamRequest(
      {
        method: "GET",
        path_query: `/drip?duration=5&numbytes=${count}&code=200&delay=0`,
        headers: {},
      },
      writeStream,
      0,
    );

    expect(streamData).toEqual("*".repeat(count));
  });

  it("proxy streams non-JSON data", async () => {
    const writeStream = new PassThrough();
    let streamData = "";
    writeStream.on("data", (chunk) => {
      streamData += chunk;
    });

    await proxyStreamRequest(
      {
        method: "GET",
        path_query: `/html`,
        headers: {},
      },
      writeStream,
      0,
    );

    expect(streamData).toMatch("<!DOCTYPE html>");
  });

  it.for([401, 403, 429, 500, 503, 504])(
    "4xx/5xx HTTP codes return error",
    async (statusCode: number) => {
      const writeStream = new PassThrough();
      const response: ProxyJSONResponse = (await proxyStreamRequest(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          headers: {},
        },
        writeStream,
        3,
      )) as ProxyJSONResponse;

      expect(response.error);
      expect(response.status).toEqual(statusCode);
    },
  );

  it("stream proxy subcommand terminates with SIGTERM on timeout", async () => {
    const writeStream = new PassThrough();
    await expect(
      proxyStreamRequest(
        {
          method: "GET",
          path_query: "/delay/10",
          headers: {},
        },
        writeStream,
        1,
      ),
    ).rejects.toThrowError("Process terminated with signal SIGTERM");
  });

  it("stream proxy subcommand aborts", async () => {
    const abortController = new AbortController();

    const writeStream = new PassThrough();
    const proxyExec = proxyStreamRequest(
      {
        method: "GET",
        path_query: "/delay/100",
        headers: {},
      },
      writeStream,
      1,
      abortController.signal,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });
});
