import childProcess from "node:child_process";
import { channel } from "node:diagnostics_channel";
import { fileURLToPath } from "node:url";
import { Writable } from "node:stream";

import { describe, expect, it } from "vitest";

import {
  LEGACY_STREAM_JSON_MAX_BYTES,
  STREAM_CAPTURE_DIAGNOSTICS_CHANNEL,
  STREAM_METADATA_MAX_BYTES,
  proxyStreamRequestInner,
} from "../src/main/proxy";
import type { StreamCaptureDiagnostics } from "../src/main/proxy";
import type {
  ProxyCommand,
  ProxyJSONResponse,
  ProxyRequest,
  ProxyStreamResponse,
  ms,
} from "../src/types";

const LEGACY_PROXY_FIXTURE = fileURLToPath(
  new URL("./fixtures/legacy-proxy.mjs", import.meta.url),
);

class CountingWritable extends Writable {
  bytesWritten = 0;

  override _write(
    chunk: Buffer,
    _encoding: BufferEncoding,
    callback: (error?: Error | null) => void,
  ): void {
    this.bytesWritten += chunk.length;
    callback();
  }
}

function legacyProxyCommand(mode: string, argument = "0"): ProxyCommand {
  return {
    command: process.execPath,
    options: [LEGACY_PROXY_FIXTURE, mode, argument],
    env: new Map(),
    timeout: 60_000 as ms,
  };
}

function newProxyCommand(): ProxyCommand {
  return {
    command: sdProxyCommand,
    options: [],
    env: new Map([
      ["SD_PROXY_ORIGIN", sdProxyOrigin],
      ["DISABLE_TOR", "yes"],
    ]),
    timeout: 20_000 as ms,
  };
}

function streamRequest(): ProxyRequest {
  return { method: "GET", path_query: "/compatibility", headers: {} };
}

async function invokeNewApp(command: ProxyCommand, request = streamRequest()) {
  const sink = new CountingWritable();
  const response = await proxyStreamRequestInner(request, command, sink);
  return { response, bytesWritten: sink.bytesWritten };
}

async function captureNewProxy(pathQuery: string) {
  const command = newProxyCommand();
  return new Promise<{ stdout: Buffer; stderr: string }>((resolve, reject) => {
    const subprocess = childProcess.spawn(command.command, command.options, {
      env: Object.fromEntries(command.env),
      timeout: command.timeout,
    });
    const stdoutChunks: Buffer[] = [];
    let stderr = "";
    subprocess.stdout.on("data", (chunk: Buffer) => stdoutChunks.push(chunk));
    subprocess.stderr.on("data", (chunk: Buffer) => {
      stderr += chunk.toString();
    });
    subprocess.on("error", reject);
    subprocess.on("close", (code) => {
      if (code !== 0) {
        reject(new Error(`Proxy fixture exited with code ${code}: ${stderr}`));
        return;
      }
      resolve({ stdout: Buffer.concat(stdoutChunks), stderr });
    });
    subprocess.stdin.write(
      JSON.stringify({
        method: "GET",
        path_query: pathQuery,
        stream: true,
        headers: {},
        timeout: 20,
      }) + "\n",
    );
  });
}

function consumeAsLegacyApp(result: { stdout: Buffer; stderr: string }) {
  try {
    const response = JSON.parse(result.stdout.toString());
    const status = response["status"];
    if (!status) {
      throw new Error("Legacy JSON response has no status");
    }
    return {
      error: (status >= 400 && status < 500) || (status >= 500 && status < 600),
      data: response["body"],
      status,
    };
  } catch {
    const metadata = JSON.parse(result.stderr);
    return {
      complete: true,
      sha256sum: metadata["headers"]["etag"] || "",
    };
  }
}

describe("new app with legacy proxy", () => {
  it("accepts a successful legacy stream", async () => {
    const { response, bytesWritten } = await invokeNewApp(
      legacyProxyCommand("success", "16"),
    );
    expect(response).toMatchObject({
      complete: true,
      bytesWritten: 16,
      sha256sum: "sha256:legacy-proxy",
    });
    expect(bytesWritten).toBe(16);
  });

  it("accepts an empty successful legacy stream", async () => {
    const { response, bytesWritten } = await invokeNewApp(
      legacyProxyCommand("empty"),
    );
    expect(response).toMatchObject({
      complete: true,
      bytesWritten: 0,
      sha256sum: "sha256:legacy-proxy",
    });
    expect(bytesWritten).toBe(0);
  });

  it.for([401, 403, 404, 500])(
    "preserves legacy HTTP %i error responses",
    async (status) => {
      const { response } = await invokeNewApp(
        legacyProxyCommand("status", String(status)),
      );
      expect(response).toMatchObject({
        error: true,
        data: `legacy error ${status}`,
        status,
      } satisfies Partial<ProxyJSONResponse>);
    },
  );

  it("rejects malformed legacy metadata", async () => {
    await expect(
      invokeNewApp(legacyProxyCommand("malformed-metadata")),
    ).rejects.toContain("Error reading metadata from proxy stderr");
  });

  it("rejects oversized legacy metadata", async () => {
    await expect(
      invokeNewApp(
        legacyProxyCommand(
          "oversized-metadata",
          String(STREAM_METADATA_MAX_BYTES + 1),
        ),
      ),
    ).rejects.toContain("Proxy stderr exceeded");
  });

  it("rejects a legacy JSON response above the compatibility limit", async () => {
    await expect(
      invokeNewApp(
        legacyProxyCommand(
          "oversized-error",
          String(LEGACY_STREAM_JSON_MAX_BYTES + 1),
        ),
      ),
    ).rejects.toContain("exceeded");
  });

  it("streams 64 and 256 MiB with constant compatibility memory", async () => {
    const diagnostics: StreamCaptureDiagnostics[] = [];
    const diagnosticsChannel = channel(STREAM_CAPTURE_DIAGNOSTICS_CHANNEL);
    const onDiagnostics = (message: unknown) => {
      diagnostics.push(message as StreamCaptureDiagnostics);
    };
    diagnosticsChannel.subscribe(onDiagnostics);
    try {
      for (const mebibytes of [64, 256]) {
        const payloadBytes = mebibytes * 1024 * 1024;
        const { response, bytesWritten } = await invokeNewApp(
          legacyProxyCommand("success", String(payloadBytes)),
        );
        expect(response).toMatchObject({
          complete: true,
          bytesWritten: payloadBytes,
          sha256sum: "sha256:legacy-proxy",
        } satisfies Partial<ProxyStreamResponse>);
        expect(bytesWritten).toBe(payloadBytes);
      }
      expect(diagnostics).toEqual(
        [64, 256].map((mebibytes) =>
          expect.objectContaining({
            stdoutBytesObserved: mebibytes * 1024 * 1024,
            legacyBytesCaptured: LEGACY_STREAM_JSON_MAX_BYTES,
          }),
        ),
      );
    } finally {
      diagnosticsChannel.unsubscribe(onDiagnostics);
    }
  }, 120_000);
});

describe("legacy app wire protocol with new proxy", () => {
  it("keeps successful stream metadata backward compatible", async () => {
    const result = await captureNewProxy("/bytes/16");
    const metadata = JSON.parse(result.stderr);
    expect(result.stdout).toHaveLength(16);
    expect(metadata.headers).toBeTypeOf("object");
    expect(consumeAsLegacyApp(result)).toMatchObject({ complete: true });
  });

  it("keeps empty stream metadata backward compatible", async () => {
    const result = await captureNewProxy("/status/204");
    const metadata = JSON.parse(result.stderr);
    expect(result.stdout).toHaveLength(0);
    expect(metadata.headers).toBeTypeOf("object");
    expect(consumeAsLegacyApp(result)).toMatchObject({ complete: true });
  });

  it.for([401, 403, 404, 500])(
    "keeps HTTP %i errors as legacy JSON envelopes",
    async (status) => {
      const result = await captureNewProxy(`/status/${status}`);
      expect(result.stderr).toBe("");
      expect(JSON.parse(result.stdout.toString())).toMatchObject({
        status,
        headers: expect.any(Object),
        body: expect.any(String),
      });
      expect(consumeAsLegacyApp(result)).toMatchObject({
        error: true,
        status,
      });
    },
  );

  it("preserves a bounded HTTP error body", async () => {
    const pathQuery = "/drip?duration=0&numbytes=16&code=401&delay=0";
    const legacyResult = await captureNewProxy(pathQuery);
    expect(JSON.parse(legacyResult.stdout.toString())).toMatchObject({
      status: 401,
      body: "*".repeat(16),
    });
    expect(consumeAsLegacyApp(legacyResult)).toMatchObject({
      error: true,
      data: "*".repeat(16),
      status: 401,
    });

    const { response } = await invokeNewApp(newProxyCommand(), {
      method: "GET",
      path_query: pathQuery,
      headers: {},
    });
    expect(response).toMatchObject({
      error: true,
      data: "*".repeat(16),
      status: 401,
    } satisfies Partial<ProxyJSONResponse>);
  });
});
