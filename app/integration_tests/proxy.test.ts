import { describe, expect, it } from "vitest";

import { PassThrough } from "node:stream";

import {
  proxyJSONRequestInner,
  proxyStreamRequestInner,
} from "../src/main/proxy";
import {
  JSONObject,
  ProxyCommand,
  ProxyJSONResponse,
  ProxyStreamResponse,
  ms,
} from "../src/types";

const proxyCommand = (timeout: number): ProxyCommand => {
  return {
    command: sdProxyCommand,
    options: [],
    env: new Map([
      ["SD_PROXY_ORIGIN", sdProxyOrigin],
      ["DISABLE_TOR", "yes"],
    ]),
    timeout: timeout as ms,
  };
};

describe("Test executing JSON proxy commands against httpbin", async () => {
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("successful JSON response", async () => {
    const result = await proxyJSONRequestInner(
      {
        method: "GET",
        path_query: "/json",
        headers: {},
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect(result.headers.get("content-type")).toEqual("application/json");
  });

  it.for([200, 204, 404])(
    "2xx and 404 HTTP codes are passed through cleanly",
    async (statusCode: number) => {
      const result = await proxyJSONRequestInner(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          headers: {},
        },
        proxyCommand(1000),
      );

      expect(result.status).toEqual(statusCode);
    },
  );

  it.for([401, 403, 429])(
    "4xx HTTP codes returns error: true response",
    async (statusCode: number) => {
      const result = await proxyJSONRequestInner(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          headers: {},
        },
        proxyCommand(1000),
      );
      expect(result.error);
      expect(result.status).toEqual(statusCode);
    },
  );

  it.for([500, 503, 504])(
    "5xx HTTP codes returns error: true response",
    async (statusCode: number) => {
      const result = await proxyJSONRequestInner(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          headers: {},
        },
        proxyCommand(1000),
      );
      expect(result.error);
      expect(result.status).toEqual(statusCode);
    },
  );

  it("path query with query parameters", async () => {
    const result = await proxyJSONRequestInner(
      {
        method: "GET",
        path_query: "/get?foo=bar",
        headers: {},
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect((result.data! as JSONObject)["args"]).toEqual({ foo: "bar" });
  });

  it("proxy subcommand terminates with SIGTERM on timeout", async () => {
    await expect(
      proxyJSONRequestInner(
        {
          method: "GET",
          path_query: "/delay/10",
          headers: {},
        },
        proxyCommand(100),
      ),
    ).rejects.toThrowError("Process terminated with signal SIGTERM");
  });

  it("proxy subcommand aborts", async () => {
    const abortController = new AbortController();
    const command = proxyCommand(10_000);
    command.abortSignal = abortController.signal;

    const proxyExec = proxyJSONRequestInner(
      {
        method: "GET",
        path_query: "/delay/100",
        headers: {},
      },
      command,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });

  it("request with headers", async () => {
    const result = await proxyJSONRequestInner(
      {
        method: "GET",
        path_query: "/headers",
        headers: { "X-Test-Header": "th" },
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect((result.data! as JSONObject)["headers"]).toHaveProperty(
      "X-Test-Header",
      "th",
    );
  });

  it("request with body", async () => {
    const input = { id: 42, title: "test" };
    const result = await proxyJSONRequestInner(
      {
        method: "POST",
        path_query: "/post",
        body: JSON.stringify(input),
        headers: {},
      },
      proxyCommand(1000),
    );
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
    await proxyStreamRequestInner(
      {
        method: "GET",
        path_query: `/drip?duration=5&numbytes=${count}&code=200&delay=0`,
        headers: {},
      },
      proxyCommand(20000),
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

    await proxyStreamRequestInner(
      {
        method: "GET",
        path_query: `/html`,
        headers: {},
      },
      proxyCommand(20000),
      writeStream,
      0,
    );

    expect(streamData).toMatch("<!DOCTYPE html>");
  });

  it.for([401, 403, 429, 500, 503, 504])(
    "4xx/5xx HTTP codes return error",
    async (statusCode: number) => {
      const writeStream = new PassThrough();
      const response: ProxyJSONResponse = (await proxyStreamRequestInner(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          headers: {},
        },
        proxyCommand(1000),
        writeStream,
        3,
      )) as ProxyJSONResponse;

      expect(response.error);
      expect(response.status).toEqual(statusCode);
    },
  );

  it("stream proxy subcommand terminates with SIGTERM on timeout", async () => {
    const writeStream = new PassThrough();
    const response = (await proxyStreamRequestInner(
      {
        method: "GET",
        path_query: "/delay/10",
        headers: {},
      },
      proxyCommand(100),
      writeStream,
      1,
    )) as ProxyStreamResponse;
    expect(response.error!.message).toEqual(
      "Process terminated with signal SIGTERM",
    );
    expect(response.complete).toEqual(false);
  });

  it("stream proxy subcommand aborts", async () => {
    const abortController = new AbortController();
    const command = proxyCommand(10000);
    command.abortSignal = abortController.signal;

    const writeStream = new PassThrough();
    const proxyExec = proxyStreamRequestInner(
      {
        method: "GET",
        path_query: "/delay/100",
        headers: {},
      },
      command,
      writeStream,
      1,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });
});
