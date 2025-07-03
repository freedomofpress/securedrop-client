import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import child_process from "node:child_process";
import EventEmitter from "events";
import { Readable, Writable } from "stream";
import crypto from "crypto";
import os from "node:os";
import fs from "fs";

import {
  proxyRequestInner,
  ProxyRequest,
  proxyStreamingInner,
  ProxyStreamResponse,
} from "../src/proxy";
import { PassThrough } from "node:stream";
import path from "node:path";

vi.mock("child_process");

const mockChildProcess = (): child_process.ChildProcess => {
  const proc = new EventEmitter() as child_process.ChildProcess;

  proc.stdout = new EventEmitter() as Readable;
  proc.stderr = new EventEmitter() as Readable;
  proc.stdin = new Writable();
  proc.stdin._write = () => {};

  return proc;
};

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
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    const respData = {
      foo: "bar",
      baz: ["foo", "bar"],
      key: 123,
    };
    const respHeaders = {
      Connection: "Keep-Alive",
      "Content-Type": "text/html",
    };
    const respStatus = 200;
    const response = {
      status: respStatus,
      headers: respHeaders,
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
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    process.stdout?.emit("data", "this is not valid JSON");

    process.emit("close", 0);

    await expect(proxyExec).rejects.toThrowError(SyntaxError);
  });

  it("proxy should error on non-404 4xx response code", async () => {
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    const respData = "Rate Limited";
    const respStatus = 429;
    const response = {
      status: respStatus,
      headers: {},
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    await expect(proxyExec).rejects.toThrowError(
      `Client error ${respStatus}: ${respData}`,
    );
  });

  it("proxy should return success on 404", async () => {
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

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
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    const respData = "Service Unavailable";
    const respStatus = 503;
    const response = {
      status: respStatus,
      headers: {},
      body: respData,
    };
    process.stdout?.emit("data", JSON.stringify(response));

    process.emit("close", 0);

    await expect(proxyExec).rejects.toThrowError(
      `Server error ${respStatus}: ${respData}`,
    );
  });

  it("proxy should fail on proxy-command exit error code", async () => {
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    process.stderr?.emit("data", "error");
    process.emit("close", 1);

    await expect(proxyExec).rejects.toThrowError(
      "Process exited with non-zero code 1: error",
    );
  });

  it("proxy should handle subprocess error", async () => {
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

    process.emit("error", "error");

    await expect(proxyExec).rejects.toThrowError("error");
  });

  it("proxy should handle SIGTERM", async () => {
    const proxyExec = proxyRequestInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
    );

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
  let tempDir: string;
  let downloadPath: string;

  beforeEach(async () => {
    process = mockStreamingChildProcess();
    vi.spyOn(child_process, "spawn").mockReturnValueOnce(process);

    tempDir = await fs.promises.mkdtemp(path.join(os.tmpdir(), "testproxy-"));
    downloadPath = path.join(tempDir, crypto.randomUUID());
  });

  afterEach(() => {
    vi.restoreAllMocks();
    fs.promises.rm(tempDir, { recursive: true });
  });

  it("proxy should return ProxyStreamResponse with data on successful response", async () => {
    const respData = "Hello, world";
    const respSHA256 = "12345";
    process.stdout = Readable.from(respData);

    const proxyExec = proxyStreamingInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
      downloadPath,
    );

    setTimeout(() => {
      process.stderr.emit(
        "data",
        JSON.stringify({ headers: { etag: respSHA256 } }),
      );
      process.emit("close", 0);
    }, 10);

    const { stream_path, sha256sum } = (await proxyExec) as ProxyStreamResponse;

    await fs.readFile(stream_path, (err, data) => {
      expect(data.toString()).toEqual(respData);
    });

    expect(sha256sum).toEqual(respSHA256);
  });

  it("proxy should fail on proxy-command exit error code", async () => {
    const proxyExec = proxyStreamingInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
      downloadPath,
    );

    setTimeout(() => {
      process.stderr?.emit("data", "error");
      process.emit("close", 1);
    }, 10);

    await expect(proxyExec).rejects.toThrowError(
      "Process exited with non-zero code 1: error",
    );
  });

  it("proxy should handle subprocess error", async () => {
    const proxyExec = proxyStreamingInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
      downloadPath,
    );

    setTimeout(() => {
      process.emit("error", "error");
    }, 10);

    await expect(proxyExec).rejects.toThrowError("error");
  });

  it("proxy should handle SIGTERM", async () => {
    const proxyExec = proxyStreamingInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      100,
      downloadPath,
    );

    setTimeout(() => {
      process.emit("close", 0, "SIGTERM");
    }, 10);

    await expect(proxyExec).rejects.toThrowError(
      "Process terminated with signal SIGTERM",
    );
  });
});
