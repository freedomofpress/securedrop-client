import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import child_process from "node:child_process";
import EventEmitter from "events";
import { Readable, Writable } from "stream";

import { proxyInner, ProxyRequest } from "./proxy";

vi.mock("child_process");

const mockChildProcess = (): child_process.ChildProcess => {
  const proc = new EventEmitter() as child_process.ChildProcess;

  proc.stdout = new EventEmitter() as Readable;
  proc.stderr = new EventEmitter() as Readable;
  proc.stdin = new Writable();
  proc.stdin._write = () => {};

  return proc;
};

describe("Test executing proxy", () => {
  let process: child_process.ChildProcess;

  beforeEach(() => {
    process = mockChildProcess();
    vi.spyOn(child_process, "spawn").mockReturnValueOnce(process);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("proxy should return ProxyResponse with deserialized JSON on successful response", async () => {
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
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
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
    );

    process.stdout?.emit("data", "this is not valid JSON");

    process.emit("close", 0);

    await expect(proxyExec).rejects.toThrowError(SyntaxError);
  });

  it("proxy should error on non-404 4xx response code", async () => {
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
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
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
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
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
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
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
    );

    process.stderr?.emit("data", "error");
    process.emit("close", 1);

    await expect(proxyExec).rejects.toThrowError(
      "Process exited with non-zero code 1: error",
    );
  });

  it("proxy should handle subprocess error", async () => {
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
    );

    process.emit("error", "error");

    await expect(proxyExec).rejects.toThrowError("error");
  });

  it("proxy should handle SIGTERM", async () => {
    const proxyExec = proxyInner(
      {} as ProxyRequest,
      "mock-proxy-command",
      [],
      "",
      1000,
    );

    process.emit("close", 0, "SIGTERM");

    await expect(proxyExec).rejects.toThrowError(
      "Process terminated with signal SIGTERM",
    );
  });
});
