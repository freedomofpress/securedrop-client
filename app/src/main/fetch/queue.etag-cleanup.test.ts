import { createHash, randomUUID } from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { finished } from "node:stream/promises";
import type { Writable } from "node:stream";

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import type { DB } from "../database";
import type { Item, ItemMetadata, ProxyStreamResponse } from "../../types";
import { FetchStatus } from "../../types";
import { TaskQueue } from "./queue";

const mockProxyStreamRequest = vi.hoisted(() => vi.fn());
const mockDecryptMessage = vi.hoisted(() => vi.fn());

vi.mock("../proxy", async () => {
  const actual = await vi.importActual("../proxy");
  return {
    ...actual,
    proxyStreamRequest: mockProxyStreamRequest,
  };
});

vi.mock("../crypto", async () => {
  const actual = await vi.importActual("../crypto");
  return {
    ...actual,
    Crypto: {
      getInstance: () => ({
        decryptMessage: mockDecryptMessage,
      }),
    },
  };
});

const CIPHERTEXT = Buffer.from("downloaded ciphertext");
const CONTROL_CIPHERTEXT = Buffer.from("unrelated ciphertext");

function etagFor(content: Buffer): string {
  return `sha256:${createHash("sha256").update(content).digest("hex")}`;
}

function mockItem(metadata: ItemMetadata, fetchStatus: FetchStatus): Item {
  return {
    uuid: metadata.uuid,
    data: metadata,
    fetch_status: fetchStatus,
    fetch_progress: 0,
    plaintext: null,
    filename: null,
    decrypted_size: null,
  };
}

function createMockDB(metadata: ItemMetadata): DB {
  return {
    getItem: vi.fn(() => mockItem(metadata, FetchStatus.Initial)),
    getItemsToProcess: vi.fn(() => []),
    getSource: vi.fn(),
    completePlaintextItem: vi.fn(),
    completeFileItem: vi.fn(),
    startDownloadInProgress: vi.fn(),
    updateDownloadInProgress: vi.fn(() => true),
    setDecryptionInProgress: vi.fn(),
    setSourceMessagePreview: vi.fn(),
    failDownload: vi.fn(),
    failDecryption: vi.fn(),
    terminallyFailItem: vi.fn(),
  } as unknown as DB;
}

type QueueErrorCallback = (error: Error | null, result?: unknown) => void;

function captureDownloadErrorCallback(
  queue: TaskQueue,
  db: DB,
  itemId: string,
): QueueErrorCallback {
  db.getItemsToProcess = vi.fn(() => [itemId]);
  let errorCallback: QueueErrorCallback | undefined;
  vi.spyOn(queue.messageDownloadQueue, "push").mockImplementation(
    (_task, callback) => {
      errorCallback = callback as QueueErrorCallback;
      return undefined as unknown as ReturnType<
        typeof queue.messageDownloadQueue.push
      >;
    },
  );

  queue.queueFetches({ authToken: "test-token" });
  expect(errorCallback).toBeDefined();
  return errorCallback as QueueErrorCallback;
}

async function writeResponse(
  writer: Writable,
  content: Buffer,
  response: ProxyStreamResponse,
): Promise<ProxyStreamResponse> {
  writer.end(content);
  await finished(writer);
  return response;
}

describe("TaskQueue ETag ciphertext cleanup", () => {
  let sourceId: string;
  let sourceDownloadDirectory: string;

  beforeEach(() => {
    vi.clearAllMocks();
    sourceId = `etag-cleanup-${randomUUID()}`;
    sourceDownloadDirectory = path.join(
      fs.realpathSync(os.tmpdir()),
      "download",
      sourceId,
    );
  });

  afterEach(async () => {
    await fs.promises.rm(sourceDownloadDirectory, {
      recursive: true,
      force: true,
    });
  });

  it.each([
    ["missing", "message", undefined, "Missing ETag checksum"],
    [
      "unsupported",
      "reply",
      "md5:invalid",
      "Invalid or unsupported ETag format",
    ],
    [
      "mismatched",
      "file",
      `sha256:${"0".repeat(64)}`,
      "ETag checksum mismatch",
    ],
  ])(
    "removes only the corresponding ciphertext for a %s ETag on a %s",
    async (_case, kind, etag, expectedError) => {
      const itemId = "target-item";
      const metadata = {
        uuid: itemId,
        kind,
        source: sourceId,
        size: CIPHERTEXT.length,
      } as ItemMetadata;
      const db = createMockDB(metadata);
      const queue = new TaskQueue(db);
      const targetPath = queue.storage.downloadFilePath(metadata, {
        id: itemId,
      });
      const controlPath = queue.storage.downloadFilePath(metadata, {
        id: "control-item",
      });
      await fs.promises.writeFile(controlPath, CONTROL_CIPHERTEXT);

      mockProxyStreamRequest.mockImplementationOnce(
        async (_request, writer: Writable) => {
          const response = {
            complete: true,
            bytesWritten: CIPHERTEXT.length,
            ...(etag === undefined ? {} : { sha256sum: etag }),
          } as ProxyStreamResponse;
          return writeResponse(writer, CIPHERTEXT, response);
        },
      );

      queue.authToken = "test-token";
      await expect(queue.processDownload({ id: itemId }, db)).rejects.toThrow(
        expectedError,
      );

      expect(db.terminallyFailItem).toHaveBeenCalledWith(itemId);
      expect(fs.existsSync(targetPath)).toBe(false);
      await expect(fs.promises.readFile(controlPath)).resolves.toEqual(
        CONTROL_CIPHERTEXT,
      );
    },
  );

  it("retains ciphertext when a download failure is retryable", async () => {
    const itemId = "retryable-item";
    const metadata = {
      uuid: itemId,
      kind: "file",
      source: sourceId,
      size: CIPHERTEXT.length * 2,
    } as ItemMetadata;
    const db = createMockDB(metadata);
    const queue = new TaskQueue(db);
    const targetPath = queue.storage.downloadFilePath(metadata, {
      id: itemId,
    });

    mockProxyStreamRequest.mockImplementationOnce(
      async (_request, writer: Writable) =>
        writeResponse(writer, CIPHERTEXT, {
          complete: false,
          bytesWritten: CIPHERTEXT.length,
          error: new Error("connection closed"),
        } as ProxyStreamResponse),
    );

    queue.authToken = "test-token";
    await expect(queue.processDownload({ id: itemId }, db)).rejects.toThrow(
      "Unable to complete stream download",
    );

    expect(db.failDownload).toHaveBeenCalledWith(itemId);
    expect(db.terminallyFailItem).not.toHaveBeenCalled();
    await expect(fs.promises.readFile(targetPath)).resolves.toEqual(CIPHERTEXT);
  });

  it("preserves the ETag error when the ciphertext is already absent", async () => {
    const itemId = "already-removed-item";
    const metadata = {
      uuid: itemId,
      kind: "message",
      source: sourceId,
      size: CIPHERTEXT.length,
    } as ItemMetadata;
    const db = createMockDB(metadata);
    const queue = new TaskQueue(db);
    const targetPath = queue.storage.downloadFilePath(metadata, {
      id: itemId,
    });

    mockProxyStreamRequest.mockImplementationOnce(
      async (_request, writer: Writable) => {
        const response = await writeResponse(writer, CIPHERTEXT, {
          complete: true,
          bytesWritten: CIPHERTEXT.length,
        } as ProxyStreamResponse);
        await fs.promises.unlink(targetPath);
        return response;
      },
    );

    queue.authToken = "test-token";
    await expect(queue.processDownload({ id: itemId }, db)).rejects.toThrow(
      "Missing ETag checksum",
    );

    expect(db.terminallyFailItem).toHaveBeenCalledWith(itemId);
    expect(fs.existsSync(targetPath)).toBe(false);
  });

  it("does not write terminal status when ciphertext cleanup gets EACCES", async () => {
    const itemId = "permission-denied-item";
    const metadata = {
      uuid: itemId,
      kind: "message",
      source: sourceId,
      size: CIPHERTEXT.length,
    } as ItemMetadata;
    const db = createMockDB(metadata);
    const queue = new TaskQueue(db);
    const queueErrorCallback = captureDownloadErrorCallback(queue, db, itemId);
    const targetPath = queue.storage.downloadFilePath(metadata, {
      id: itemId,
    });
    const cleanupFailure = new Error(
      "permission denied",
    ) as NodeJS.ErrnoException;
    cleanupFailure.code = "EACCES";
    const realRm = fs.promises.rm.bind(fs.promises);
    vi.spyOn(fs.promises, "rm").mockImplementationOnce(
      async (rmPath, options) => {
        if (rmPath.toString() === targetPath) {
          throw cleanupFailure;
        }
        return realRm(rmPath, options);
      },
    );

    mockProxyStreamRequest.mockImplementationOnce(
      async (_request, writer: Writable) =>
        writeResponse(writer, CIPHERTEXT, {
          complete: true,
          bytesWritten: CIPHERTEXT.length,
        } as ProxyStreamResponse),
    );

    queue.authToken = "test-token";
    let cleanupError: unknown;
    try {
      await queue.processDownload({ id: itemId }, db);
    } catch (error) {
      cleanupError = error;
    }

    expect((cleanupError as NodeJS.ErrnoException).code).toBe("EACCES");
    queueErrorCallback(cleanupError as Error);
    queue.messageDownloadQueue.emit("task_failed", itemId, cleanupError);
    expect(db.failDownload).toHaveBeenCalledWith(itemId);
    expect(db.terminallyFailItem).not.toHaveBeenCalled();
    expect(db.getItemsToProcess).toHaveBeenCalledTimes(1);
    expect(fs.existsSync(targetPath)).toBe(true);
  });

  it("removes ciphertext before writing terminal status", async () => {
    const itemId = "terminal-write-failure-item";
    const metadata = {
      uuid: itemId,
      kind: "message",
      source: sourceId,
      size: CIPHERTEXT.length,
    } as ItemMetadata;
    const db = createMockDB(metadata);
    const queue = new TaskQueue(db);
    const queueErrorCallback = captureDownloadErrorCallback(queue, db, itemId);
    const targetPath = queue.storage.downloadFilePath(metadata, {
      id: itemId,
    });
    db.terminallyFailItem = vi.fn(() => {
      expect(fs.existsSync(targetPath)).toBe(false);
      throw new Error("terminal DB write failed");
    });

    mockProxyStreamRequest.mockImplementationOnce(
      async (_request, writer: Writable) =>
        writeResponse(writer, CIPHERTEXT, {
          complete: true,
          bytesWritten: CIPHERTEXT.length,
        } as ProxyStreamResponse),
    );

    queue.authToken = "test-token";
    let terminalWriteError: unknown;
    try {
      await queue.processDownload({ id: itemId }, db);
    } catch (error) {
      terminalWriteError = error;
    }

    expect(terminalWriteError).toEqual(
      expect.objectContaining({ message: "terminal DB write failed" }),
    );
    queueErrorCallback(terminalWriteError as Error);
    expect(db.failDownload).toHaveBeenCalledWith(itemId);
    expect(db.terminallyFailItem).toHaveBeenCalledWith(itemId);
    expect(fs.existsSync(targetPath)).toBe(false);
  });

  it("retains verified ciphertext until successful decryption", async () => {
    const itemId = "successful-item";
    const metadata = {
      uuid: itemId,
      kind: "message",
      source: sourceId,
      size: CIPHERTEXT.length,
    } as ItemMetadata;
    const db = createMockDB(metadata);
    const queue = new TaskQueue(db);
    const targetPath = queue.storage.downloadFilePath(metadata, {
      id: itemId,
    });

    mockProxyStreamRequest.mockImplementationOnce(
      async (_request, writer: Writable) =>
        writeResponse(writer, CIPHERTEXT, {
          complete: true,
          bytesWritten: CIPHERTEXT.length,
          sha256sum: etagFor(CIPHERTEXT),
        } as ProxyStreamResponse),
    );

    queue.authToken = "test-token";
    await queue.processDownload({ id: itemId }, db);
    await expect(fs.promises.readFile(targetPath)).resolves.toEqual(CIPHERTEXT);

    db.getItem = vi.fn(() =>
      mockItem(metadata, FetchStatus.DecryptionInProgress),
    );
    mockDecryptMessage.mockResolvedValueOnce("decrypted plaintext");
    await queue.processDecrypt({ id: itemId }, db);

    expect(db.completePlaintextItem).toHaveBeenCalledWith(
      itemId,
      "decrypted plaintext",
    );
    expect(fs.existsSync(targetPath)).toBe(false);
  });
});
