import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import child_process from "node:child_process";
import EventEmitter from "events";
import { Readable, Writable } from "stream";

import type {
  ProxyRequest,
  ProxyCommand,
  ProxyStreamResponse,
  ms,
} from "../types";
import { proxyJSONRequest, proxyStreamRequest } from "./proxy";
import { PassThrough } from "node:stream";

vi.mock("child_process");

const mockChildProcess = (): child_process.ChildProcess => {
  const proc = new EventEmitter() as child_process.ChildProcess;

  proc.stdout = new EventEmitter() as Readable;
  proc.stderr = new EventEmitter() as Readable;
  proc.stdin = new Writable();
  proc.stdin._write = () => {};

  return proc;
};

vi.mock("./proxy", async () => {
  const actual = await vi.importActual("./proxy");
  return {
    ...actual,
    buildProxyCommand: vi.fn(mockProxyCommand),
  };
});

const mockProxyCommand = vi.hoisted(() => (): ProxyCommand => {
  return {
    command: "",
    options: [],
    env: new Map(),
    timeout: 100 as ms,
  };
});

describe("Test executing proxy with JSON requests", () => {
  let process: child_process.ChildProcess;

  beforeEach(() => {
    process = mockChildProcess();
    vi.spyOn(child_process, "spawn").mockReturnValueOnce(process);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("proxy should return ProxyResponse with deserialized JSON on successful response", async () => {
    interface RespData {
      foo: string;
      baz: string[];
      key: number;
    }
    const respData: RespData = {
      foo: "bar",
      baz: ["foo", "bar"],
      key: 123,
    };
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    const respHeaders = new Map([
      ["Connection", "Keep-Alive"],
      ["Content-Type", "text/html"],
    ]);
    const respStatus = 200;
    const response = {
      status: respStatus,
      headers: Object.fromEntries(respHeaders),
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    const { data, status, headers } = await proxyExec;

    expect(data).toEqual(respData);
    expect(headers).toEqual(respHeaders);
    expect(status).toEqual(respStatus);
  });

  it("proxy should error on invalid JSON response data", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    process.stdout?.emit("data", "this is not valid JSON");

    process.emit("close", 0);

    await expect(proxyExec).rejects.toThrowError(SyntaxError);
  });

  it("proxy should error on non-404 4xx response code", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    const respData = "Rate Limited";
    const respStatus = 429;
    const response = {
      status: respStatus,
      headers: {},
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    const { status, error } = await proxyExec;
    expect(error);
    expect(status).toEqual(respStatus);
  });

  it("proxy should return on 404", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    const respData = "Not Found";
    const respStatus = 404;
    const response = {
      status: respStatus,
      headers: {},
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    const { data, status } = await proxyExec;

    expect(data).toEqual(respData);
    expect(status).toEqual(respStatus);
  });

  it("proxy should error on 5xx response code", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    const respData = "Service Unavailable";
    const respStatus = 503;
    const response = {
      status: respStatus,
      headers: {},
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    const { status, error } = await proxyExec;
    expect(error);
    expect(status).toEqual(respStatus);
  });

  it("proxy should fail on proxy-command exit error code", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    process.stderr?.emit("data", "error");
    process.emit("close", 1);

    await expect(proxyExec).rejects.toThrowError(
      "Process exited with non-zero code 1: error",
    );
  });

  it("proxy should handle subprocess error", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    process.emit("error", "error");

    await expect(proxyExec).rejects.toThrowError("error");
  });

  it("proxy should handle SIGTERM", async () => {
    const proxyExec = proxyJSONRequest({} as ProxyRequest);

    process.emit("close", 0, "SIGTERM");

    await expect(proxyExec).rejects.toThrowError(
      "Process terminated with signal SIGTERM",
    );
  });
});

const mockStreamingChildProcess = (): child_process.ChildProcess => {
  const proc = new EventEmitter() as child_process.ChildProcess;

  proc.stdout = new PassThrough() as Readable;
  proc.stderr = new EventEmitter() as Readable;
  proc.stdin = new Writable();
  proc.stdin._write = () => {};

  return proc;
};

describe("Test executing proxy with streaming requests", () => {
  let process: child_process.ChildProcess;
  let writeStream: PassThrough;

  beforeEach(async () => {
    process = mockStreamingChildProcess();
    vi.spyOn(child_process, "spawn").mockReturnValueOnce(process);
    writeStream = new PassThrough();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("proxy should return ProxyStreamResponse with data on successful response", async () => {
    const respData = "Hello, world";
    const respSHA256 = "12345";
    process.stdout = Readable.from(respData);

    let data = "";

    writeStream.on("data", (chunk) => {
      data += chunk;
    });

    const proxyExec = proxyStreamRequest(
      {} as ProxyRequest,

      writeStream,
    );

    if (process.stderr) {
      process.stderr.emit(
        "data",
        JSON.stringify({ headers: { etag: respSHA256 } }),
      );
    }

    setTimeout(() => {
      process.emit("close", 0);
    }, 10);

    const { sha256sum } = (await proxyExec) as ProxyStreamResponse;

    expect(data.toString()).toEqual(respData);
    expect(sha256sum).toEqual(respSHA256);
  });

  it("proxy should return on proxy-command exit error code", async () => {
    const proxyExec = proxyStreamRequest({} as ProxyRequest, writeStream);

    process.stderr?.emit("data", "error");

    setTimeout(() => {
      process.emit("close", 1);
    }, 10);

    const { complete, error } = (await proxyExec) as ProxyStreamResponse;
    expect(!complete);
    expect(error!.message).toEqual(
      "Process exited with non-zero code 1: error",
    );
  });

  it("proxy should handle subprocess error", async () => {
    const proxyExec = proxyStreamRequest({} as ProxyRequest, writeStream);

    setTimeout(() => {
      process.emit("error", "error");
    }, 10);

    await expect(proxyExec).rejects.toThrowError("error");
  });

  it("proxy should handle SIGTERM", async () => {
    const proxyExec = proxyStreamRequest({} as ProxyRequest, writeStream);

    setTimeout(() => {
      process.emit("close", 0, "SIGTERM");
    }, 10);

    const { complete, error } = (await proxyExec) as ProxyStreamResponse;
    expect(!complete);
    expect(error!.message).toEqual("Process terminated with signal SIGTERM");
  });
});
