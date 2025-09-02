import { describe, expect, it } from "vitest";

import { PassThrough } from "node:stream";

import {
  proxyJSONRequest,
  proxyStreamInner,
  proxyStreamRequest,
} from "../src/main/proxy";
import { ProxyCommand, ProxyJSONResponse, ms } from "../src/types";

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
  it("successful JSON response", async () => {
    const result = await proxyJSONRequest(
      {
        method: "GET",
        path_query: "/json",
        stream: false,
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
      const result = await proxyJSONRequest(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          stream: false,
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
      const result = await proxyJSONRequest(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          stream: false,
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
      const result = await proxyJSONRequest(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          stream: false,
          headers: {},
        },
        proxyCommand(1000),
      );
      expect(result.error);
      expect(result.status).toEqual(statusCode);
    },
  );

  it("path query with query parameters", async () => {
    const result = await proxyJSONRequest(
      {
        method: "GET",
        path_query: "/get?foo=bar",
        stream: false,
        headers: {},
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect(result.data!["args"]).toEqual({ foo: "bar" });
  });

  it("proxy subcommand terminates with SIGTERM on timeout", async () => {
    await expect(
      proxyJSONRequest(
        {
          method: "GET",
          path_query: "/delay/10",
          stream: false,
          headers: {},
        },
        proxyCommand(100),
      ),
    ).rejects.toThrowError("Process terminated with signal SIGTERM");
  });

  it("proxy subcommand aborts", async () => {
    const abortController = new AbortController();
    const command = proxyCommand(10000);
    command.abortSignal = abortController.signal;

    const proxyExec = proxyJSONRequest(
      {
        method: "GET",
        path_query: "/delay/100",
        stream: false,
        headers: {},
      },
      command,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });

  it("request with headers", async () => {
    const result = await proxyJSONRequest(
      {
        method: "GET",
        path_query: "/headers",
        stream: false,
        headers: { "X-Test-Header": "th" },
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect(result.data!["headers"]).toHaveProperty("X-Test-Header", "th");
  });

  it("request with body", async () => {
    const input = { id: 42, title: "test" };
    const result = await proxyJSONRequest(
      {
        method: "POST",
        path_query: "/post",
        stream: false,
        body: JSON.stringify(input),
        headers: {},
      },
      proxyCommand(1000),
    );
    expect(result.status).toEqual(200);
    expect(result.data!["json"]).toEqual(input);
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
    await proxyStreamInner(
      {
        method: "GET",
        path_query: `/drip?duration=5&numbytes=${count}&code=200&delay=0`,
        stream: true,
        headers: {},
      },
      proxyCommand(20000),
      writeStream,
    );

    expect(streamData).toEqual("*".repeat(count));
  });

  it("proxy streams non-JSON data", async () => {
    const writeStream = new PassThrough();
    let streamData = "";
    writeStream.on("data", (chunk) => {
      streamData += chunk;
    });

    await proxyStreamInner(
      {
        method: "GET",
        path_query: `/html`,
        stream: true,
        headers: {},
      },
      proxyCommand(20000),
      writeStream,
    );

    expect(streamData).toMatch("<!DOCTYPE html>");
  });

  it.for([401, 403, 429, 500, 503, 504])(
    "4xx/5xx HTTP codes return error",
    async (statusCode: number) => {
      const response: ProxyJSONResponse = (await proxyStreamRequest(
        {
          method: "GET",
          path_query: `/status/${statusCode}`,
          stream: true,
          headers: {},
        },
        proxyCommand(1000),
        "/tmp/baz",
        3,
      )) as ProxyJSONResponse;

      expect(response.error);
      expect(response.status).toEqual(statusCode);
    },
  );

  it("stream proxy subcommand terminates with SIGTERM on timeout", async () => {
    await expect(
      proxyStreamRequest(
        {
          method: "GET",
          path_query: "/delay/10",
          stream: false,
          headers: {},
        },
        proxyCommand(100),
        "/tmp/bar",
        1,
      ),
    ).rejects.toThrowError("Process terminated with signal SIGTERM");
  });

  it("stream proxy subcommand aborts", async () => {
    const abortController = new AbortController();
    const command = proxyCommand(10000);
    command.abortSignal = abortController.signal;

    const proxyExec = proxyStreamRequest(
      {
        method: "GET",
        path_query: "/delay/100",
        stream: true,
        headers: {},
      },
      command,
      "/tmp/bar",
      1,
    );

    abortController.abort();

    await expect(proxyExec).rejects.toThrowError("The operation was aborted");
  });
});
