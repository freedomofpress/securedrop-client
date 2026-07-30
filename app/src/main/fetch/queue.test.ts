import { describe, it, expect, vi, beforeEach, Mock } from "vitest";
import { createHash } from "node:crypto";
import fs from "fs";
import os from "os";
import path from "path";
import { PassThrough, Readable } from "stream";
import { MessagePort as WorkerMessagePort } from "worker_threads";

import { TaskQueue } from "./queue";
import { CryptoError } from "../crypto";
import {
  FetchStatus,
  ItemMetadata,
  Item,
  ProxyStreamResponse,
} from "../../types";
import { DB } from "../database";

// Mocks
const mockProxyStreamRequest = vi.hoisted(() => {
  return vi.fn();
});
const MOCK_FILE_CONTENT = vi.hoisted(() => Buffer.from("fake file content"));
vi.mock("../proxy", async () => {
  const actual = await vi.importActual("../proxy");
  return {
    ...actual,
    proxyStreamRequest: mockProxyStreamRequest,
  };
});

const mockCrypto = {
  decryptMessage: vi.fn(),
  decryptFile: vi.fn(),
};
vi.mock("../crypto", async () => {
  const actual = await vi.importActual("../crypto");
  return {
    ...actual,
    Crypto: {
      getInstance: () => mockCrypto,
    },
    CryptoError: class CryptoError extends Error {},
  };
});

// Mock fs for file operations
vi.mock("fs", () => ({
  default: {
    promises: {
      mkdir: vi.fn(),
      writeFile: vi.fn(),
      readFile: vi.fn(),
      unlink: vi.fn(),
      stat: vi.fn(() => Promise.resolve({ size: 1024 })),
    },
    createWriteStream: vi.fn(() => new PassThrough()),
    createReadStream: vi.fn(() => Readable.from([MOCK_FILE_CONTENT])),
  },
  existsSync: vi.fn(() => true),
  realpathSync: vi.fn((path) => path),
  mkdtempSync: vi.fn((prefix) => prefix + "XXXXXX"),
  mkdirSync: vi.fn(),
  rmSync: vi.fn(),
}));

// SHA-256 of MOCK_FILE_CONTENT — matches what the mocked createReadStream returns
const FILE_ETAG = etagFor(MOCK_FILE_CONTENT);

// Helper to build the "sha256:<hex>" ETag for a given buffer
function etagFor(buf: Buffer): string {
  return `sha256:${createHash("sha256").update(buf).digest("hex")}`;
}

// Helper to create mock DB with specific methods
function createMockDB() {
  return {
    getItemsToProcess: vi.fn(),
    getItem: vi.fn(),
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

function mockItem(
  metadata: ItemMetadata,
  fetch_status: FetchStatus,
  fetch_progress: number | null = null,
): Item {
  return {
    uuid: "id",
    data: metadata,
    fetch_status,
    fetch_progress,
    plaintext: null,
    filename: null,
    decrypted_size: null,
    doubleEncryptedKeyFingerprint: null,
  };
}

// Helper: mock createReadStream to return the given buffer (used for ETag verification)
function mockReadStreamFor(buf: Buffer) {
  (fs.createReadStream as ReturnType<typeof vi.fn>).mockReturnValueOnce(
    Readable.from([buf]),
  );
}

describe("TaskQueue - Four-Queue Download and Decryption", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockCrypto.decryptMessage.mockReset();
    mockCrypto.decryptFile.mockReset();
  });

  describe("Message Download Phase", () => {
    it("should download a message and write ciphertext to disk, then transition to DecryptionInProgress", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted message data");
      mockReadStreamFor(encryptedBuffer);

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      // Verify download phase
      expect(db.startDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/msg1/download",
        }),
        expect.any(PassThrough),
        0,
        expect.any(AbortSignal),
        20000,
        expect.any(Function),
      );

      // Ciphertext is written to disk via createWriteStream (not in-memory)
      expect(fs.createWriteStream).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
        expect.objectContaining({ flags: "w" }),
      );

      // Transitions to decrypt phase
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");

      // Decryption did NOT happen in the download phase
      expect(mockCrypto.decryptMessage).not.toHaveBeenCalled();
    });

    it("should download a reply and write ciphertext to disk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "reply",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted reply data");
      mockReadStreamFor(encryptedBuffer);

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "reply1" }, db);

      // Verify reply uses correct API endpoint
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/replies/reply1/download",
        }),
        expect.any(PassThrough),
        0,
        expect.any(AbortSignal),
        20000,
        expect.any(Function),
      );

      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("reply1");
      expect(mockCrypto.decryptMessage).not.toHaveBeenCalled();
    });

    it("should retry a failed message download when status is FailedDownloadRetryable", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      // First attempt: download fails
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDownloadRetryable, 50),
        );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 50,
        error: new Error("Network error"),
      });

      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.startDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.updateDownloadInProgress).toHaveBeenCalledWith("msg1", 50);
      expect(db.failDownload).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();

      // Second attempt: download succeeds
      const encryptedBuffer = Buffer.from("encrypted message data");
      mockReadStreamFor(encryptedBuffer);
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      // Download now progressing
      db.getItem = vi
        .fn()
        .mockReturnValue(
          mockItem(metadata, FetchStatus.DownloadInProgress, 50),
        );

      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(2);
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
    });
  });

  describe("Message Decrypt Phase", () => {
    it("should decrypt a message by reading ciphertext from disk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      const encryptedBuffer = Buffer.from("encrypted message data");
      const decryptedContent = "decrypted message content";
      const innerFingerprint = "A".repeat(40);
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: decryptedContent,
        doubleEncryptedKeyFingerprint: innerFingerprint,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      // Reads ciphertext from disk (not from memory)
      expect(fs.promises.readFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(mockCrypto.decryptMessage).toHaveBeenCalledWith(
        encryptedBuffer,
        expect.any(AbortSignal),
      );
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
        innerFingerprint,
      );
      // Ciphertext file cleaned up after success
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });

    it("should decrypt a reply by reading ciphertext from disk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "reply",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      const encryptedBuffer = Buffer.from("encrypted reply data");
      const decryptedContent = "decrypted reply content";
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: decryptedContent,
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "reply1" }, db);

      expect(fs.promises.readFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "reply1",
        decryptedContent,
        null,
      );
      expect(fs.promises.unlink).toHaveBeenCalled();
    });

    it("should retry decryption from disk when status is FailedDecryptionRetryable", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
      );

      const encryptedBuffer = Buffer.from("encrypted message data");
      const decryptedContent = "decrypted message content";
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: decryptedContent,
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      // No download — reads directly from disk
      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(fs.promises.readFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
        null,
      );
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });

    it("should fail decryption and leave ciphertext on disk for retry", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      const encryptedBuffer = Buffer.from("encrypted message data");
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockRejectedValueOnce(
        new CryptoError("Decryption failed"),
      );

      const queue = new TaskQueue(db);

      await expect(queue.processDecrypt({ id: "msg1" }, db)).rejects.toThrow(
        "Decryption failed",
      );

      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(db.failDecryption).toHaveBeenCalledWith("msg1");
      // Ciphertext stays on disk for the next retry attempt
      expect(fs.promises.unlink).not.toHaveBeenCalled();
    });
  });

  describe("Full Message Flow (download → decrypt)", () => {
    it("should download to disk then decrypt out of band", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      const encryptedBuffer = Buffer.from("encrypted message data");
      const decryptedContent = "decrypted message content";

      // Phase 1: download
      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));
      mockReadStreamFor(encryptedBuffer);
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(mockCrypto.decryptMessage).not.toHaveBeenCalled();

      // Phase 2: decrypt (out of band, separate call)
      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: decryptedContent,
        doubleEncryptedKeyFingerprint: null,
      });

      await queue.processDecrypt({ id: "msg1" }, db);

      // Download did not run again
      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(1);
      expect(fs.promises.readFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
        null,
      );
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });
  });

  describe("File Download Phase", () => {
    it("should download a file to disk and transition to DecryptionInProgress", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DownloadInProgress, 0),
      );

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: FILE_ETAG,
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(db.startDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/msg1/download",
        }),
        expect.any(PassThrough),
        0,
        expect.any(AbortSignal),
        55000,
        expect.any(Function),
      );

      // Transitions to decrypt phase
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");

      // Decryption did NOT happen in the download phase
      expect(mockCrypto.decryptFile).not.toHaveBeenCalled();
    });

    it("should send throttled progress updates and update db for each chunk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-progress",
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DownloadInProgress, 0),
      );
      db.getSource = vi.fn(() => ({}) as never);

      // Mock Date.now to control throttling intervals
      const nowSpy = vi
        .spyOn(Date, "now")
        .mockReturnValueOnce(200) // first progress -> postMessage
        .mockReturnValueOnce(250) // within throttle window -> no postMessage
        .mockReturnValueOnce(500) // outside throttle window -> second postMessage
        .mockReturnValue(500);

      mockProxyStreamRequest.mockImplementation(
        async (_req, _writer, _offset, _abort, _timeout, onProgress) => {
          onProgress?.(10);
          onProgress?.(20);
          onProgress?.(30);
          return {
            complete: true,
            bytesWritten: 30,
            sha256sum: FILE_ETAG,
          } as ProxyStreamResponse;
        },
      );

      const mockPort = { postMessage: vi.fn() } as unknown as WorkerMessagePort;
      const queue = new TaskQueue(db, mockPort);
      queue.authToken = "test-token";

      await queue.processDownload({ id: "file-uuid-progress" }, db);

      const updateDownloadMock = db.updateDownloadInProgress as unknown as Mock;
      const progressCalls = updateDownloadMock.mock.calls;
      expect(progressCalls.map((call) => call[1])).toEqual([10, 20, 30]);

      // One throttled progress post plus the final item update from processDownload's finally
      expect(mockPort.postMessage).toHaveBeenCalledTimes(2);

      nowSpy.mockRestore();
    });

    it("should retry a failed file download when status is FailedDownloadRetryable", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-3",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.DownloadInProgress, 0),
        )
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDownloadRetryable, 30),
        );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 50,
        error: new Error("Network error"),
      });

      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.startDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.updateDownloadInProgress).toHaveBeenCalledWith("msg1", 50);
      expect(db.failDownload).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100,
        sha256sum: FILE_ETAG,
      });

      // Download now progressing
      db.getItem = vi
        .fn()
        .mockReturnValue(
          mockItem(metadata, FetchStatus.DownloadInProgress, 50),
        );

      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(2);
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
    });
  });

  describe("File Decrypt Phase", () => {
    it("should decrypt a file from disk on first attempt", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      mockCrypto.decryptFile.mockResolvedValue({
        finalPath: "/securedrop/source1/plaintext.txt",
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      const downloadPath = path.join(
        os.tmpdir(),
        "download",
        "source1",
        "msg1",
        "encrypted.gpg",
      );
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(mockCrypto.decryptFile).toHaveBeenCalledWith(
        expect.any(Object), // storage
        expect.any(Object), // itemDirectory
        downloadPath,
        expect.any(AbortSignal),
      );
      expect(db.completeFileItem).toHaveBeenCalledWith(
        "msg1",
        "/securedrop/source1/plaintext.txt",
        expect.any(Number),
        null,
      );
    });

    it("should retry file decryption from disk when status is FailedDecryptionRetryable", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-2",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
      );

      mockCrypto.decryptFile.mockResolvedValue({
        finalPath: "/securedrop/source1/plaintext.txt",
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      // No download
      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.completeFileItem).toHaveBeenCalledWith(
        "msg1",
        "/securedrop/source1/plaintext.txt",
        expect.any(Number),
        null,
      );
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });

    it("should fail file decryption and leave encrypted file on disk for retry", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-2",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      mockCrypto.decryptFile.mockRejectedValueOnce(
        new CryptoError("Decryption failed"),
      );

      const queue = new TaskQueue(db);

      await expect(queue.processDecrypt({ id: "msg1" }, db)).rejects.toThrow(
        "Decryption failed",
      );

      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(db.failDecryption).toHaveBeenCalledWith("msg1");
      // Encrypted file stays on disk for the next retry attempt
      expect(fs.promises.unlink).not.toHaveBeenCalled();
    });
  });

  describe("Edge Cases and Error Handling", () => {
    it.each([
      { status: FetchStatus.Complete, label: "complete" },
      { status: FetchStatus.FailedTerminal, label: "terminally failed" },
      { status: FetchStatus.Paused, label: "paused" },
      { status: FetchStatus.Cancelled, label: "cancelled" },
    ])(
      "processDownload should skip items that are $label",
      async ({ status }) => {
        const db = createMockDB();
        const metadata = {
          kind: "message",
          source: "source1",
          size: 1000,
        } as ItemMetadata;

        db.getItem = vi.fn(() => mockItem(metadata, status, 0));

        const queue = new TaskQueue(db);
        queue.authToken = "test-token";
        await queue.processDownload({ id: "msg1" }, db);

        expect(mockProxyStreamRequest).not.toHaveBeenCalled();
        expect(db.startDownloadInProgress).not.toHaveBeenCalled();
        expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
      },
    );

    it.each([
      { status: FetchStatus.Complete, label: "complete" },
      { status: FetchStatus.FailedTerminal, label: "terminally failed" },
      { status: FetchStatus.Paused, label: "paused" },
      { status: FetchStatus.Cancelled, label: "cancelled" },
    ])(
      "processDecrypt should skip items that are $label",
      async ({ status }) => {
        const db = createMockDB();
        const metadata = {
          kind: "message",
          source: "source1",
          size: 1000,
        } as ItemMetadata;

        db.getItem = vi.fn(() => mockItem(metadata, status, 0));

        const queue = new TaskQueue(db);
        await queue.processDecrypt({ id: "msg1" }, db);

        expect(mockCrypto.decryptMessage).not.toHaveBeenCalled();
        expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
      },
    );

    it("processDownload should skip items that are scheduled for deletion", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.startDownloadInProgress).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("processDownload should skip items already in decrypt phase (guard against mis-routing)", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.startDownloadInProgress).not.toHaveBeenCalled();
    });

    it("processDecrypt should skip items still in download phase (guard against mis-routing)", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      expect(mockCrypto.decryptMessage).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should handle server error responses during download", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        data: "Server error message",
        error: true,
        status: 500,
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "Received error from server with status 500",
      );

      expect(db.failDownload).toHaveBeenCalledWith("msg1");
    });

    it("should handle file read errors during message decryption", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
      );

      fs.promises.readFile = vi
        .fn()
        .mockRejectedValue(new Error("File not found"));

      const queue = new TaskQueue(db);

      await expect(queue.processDecrypt({ id: "msg1" }, db)).rejects.toThrow(
        "Failed to load encrypted data from disk",
      );

      expect(db.failDecryption).toHaveBeenCalledWith("msg1");
    });

    it("processDownload should return early when authToken is null", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      // authToken is null
      const queue = new TaskQueue(db);
      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.startDownloadInProgress).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("processDownload should return early for files when authToken is null", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.DownloadInProgress, 0),
      );

      // authToken is null
      const queue = new TaskQueue(db);
      await queue.processDownload({ id: "file1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.startDownloadInProgress).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should handle unsupported item kinds in processDownload", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "unknown",
        source: "source1",
      } as unknown as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      await expect(queue.processDownload({ id: "item1" }, db)).rejects.toThrow(
        "Unsupported item kind: unknown",
      );
    });
  });

  describe("Queue Integration — four-queue routing", () => {
    it("should route messages/replies to messageDownloadQueue and files to fileDownloadQueue", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["message1", "file1", "reply1"]);
      db.getItem = vi.fn((id) => {
        if (id === "message1") {
          return mockItem(
            {
              kind: "message",
              source: "source1",
              uuid: "message1",
            } as ItemMetadata,
            FetchStatus.Initial,
          );
        }
        if (id === "reply1") {
          return mockItem(
            {
              kind: "reply",
              source: "source1",
              uuid: "reply1",
            } as ItemMetadata,
            FetchStatus.Initial,
          );
        }
        if (id === "file1") {
          return mockItem(
            {
              kind: "file",
              source: "source1",
              uuid: "file1",
              size: 1000,
            } as ItemMetadata,
            FetchStatus.DownloadInProgress,
          );
        }
        return null;
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.messageDecryptQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");
      vi.spyOn(queue.fileDecryptQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
      // 2 messages/replies in download phase → messageDownloadQueue
      expect(queue.messageDownloadQueue.push).toHaveBeenCalledTimes(2);
      // 1 file in download phase → fileDownloadQueue
      expect(queue.fileDownloadQueue.push).toHaveBeenCalledTimes(1);
      // Neither decrypt queue receives any tasks
      expect(queue.messageDecryptQueue.push).not.toHaveBeenCalled();
      expect(queue.fileDecryptQueue.push).not.toHaveBeenCalled();
      expect(queue.authToken).toBe("test-token");
    });

    it("should route items in decrypt phase to the decrypt queues", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => [
        "msgDecrypt",
        "replyDecrypt",
        "fileDecrypt",
      ]);
      db.getItem = vi.fn((id) => {
        if (id === "msgDecrypt") {
          return mockItem(
            { kind: "message", source: "s1", uuid: id } as ItemMetadata,
            FetchStatus.DecryptionInProgress,
          );
        }
        if (id === "replyDecrypt") {
          return mockItem(
            { kind: "reply", source: "s1", uuid: id } as ItemMetadata,
            FetchStatus.FailedDecryptionRetryable,
          );
        }
        if (id === "fileDecrypt") {
          return mockItem(
            {
              kind: "file",
              source: "s1",
              uuid: id,
              size: 1000,
            } as ItemMetadata,
            FetchStatus.DecryptionInProgress,
          );
        }
        return null;
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.messageDecryptQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");
      vi.spyOn(queue.fileDecryptQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      expect(queue.messageDecryptQueue.push).toHaveBeenCalledTimes(2);
      expect(queue.fileDecryptQueue.push).toHaveBeenCalledTimes(1);
      expect(queue.messageDownloadQueue.push).not.toHaveBeenCalled();
      expect(queue.fileDownloadQueue.push).not.toHaveBeenCalled();
    });

    it("should route mixed-phase items to the correct queues", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => [
        "msgDownload",
        "msgDecrypt",
        "fileDownload",
        "fileDecrypt",
      ]);
      db.getItem = vi.fn((id) => {
        const statusMap: Record<string, [string, FetchStatus]> = {
          msgDownload: ["message", FetchStatus.Initial],
          msgDecrypt: ["message", FetchStatus.DecryptionInProgress],
          fileDownload: ["file", FetchStatus.DownloadInProgress],
          fileDecrypt: ["file", FetchStatus.FailedDecryptionRetryable],
        };
        const [kind, status] = statusMap[id];
        return mockItem(
          { kind, source: "s1", uuid: id, size: 1000 } as ItemMetadata,
          status,
        );
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.messageDecryptQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");
      vi.spyOn(queue.fileDecryptQueue, "push");

      queue.queueFetches({ authToken: "tok" });

      expect(queue.messageDownloadQueue.push).toHaveBeenCalledTimes(1);
      expect(queue.messageDecryptQueue.push).toHaveBeenCalledTimes(1);
      expect(queue.fileDownloadQueue.push).toHaveBeenCalledTimes(1);
      expect(queue.fileDecryptQueue.push).toHaveBeenCalledTimes(1);
    });

    it("should handle queue errors with failDownload", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["item1"]);
      db.getItem = vi.fn(() =>
        mockItem(
          { kind: "message", source: "source1", uuid: "item1" } as ItemMetadata,
          FetchStatus.Initial,
        ),
      );

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      const pushCall = vi.mocked(queue.messageDownloadQueue.push).mock.calls[0];
      expect(pushCall).toBeDefined();
      expect(pushCall[1]).toBeTypeOf("function");

      const errorCallback = pushCall[1] as (
        err: Error | null,
        result?: unknown,
      ) => void;
      errorCallback(new Error("Task failed"));

      expect(db.failDownload).toHaveBeenCalledWith("item1");
    });

    it("should not throw if failDownload throws in queue error callback", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["item1"]);
      db.getItem = vi.fn(() =>
        mockItem(
          { kind: "message", source: "source1", uuid: "item1" } as ItemMetadata,
          FetchStatus.Initial,
        ),
      );
      db.failDownload = vi.fn(() => {
        throw new Error("failDownload failed");
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      const pushCall = vi.mocked(queue.messageDownloadQueue.push).mock.calls[0];
      const errorCallback = pushCall[1] as (
        err: Error | null,
        result?: unknown,
      ) => void;

      expect(() => errorCallback(new Error("Task failed"))).not.toThrow();
      expect(db.failDownload).toHaveBeenCalledWith("item1");
    });

    it("should not throw if postMessage throws in queue error callback", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["item1"]);
      db.getItem = vi.fn(() =>
        mockItem(
          { kind: "message", source: "source1", uuid: "item1" } as ItemMetadata,
          FetchStatus.Initial,
        ),
      );

      const mockPort = {
        postMessage: vi.fn(() => {
          throw new Error("postMessage failed");
        }),
      } as unknown as WorkerMessagePort;

      const queue = new TaskQueue(db, mockPort);
      vi.spyOn(queue.messageDownloadQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      const pushCall = vi.mocked(queue.messageDownloadQueue.push).mock.calls[0];
      const errorCallback = pushCall[1] as (
        err: Error | null,
        result?: unknown,
      ) => void;

      expect(() => errorCallback(new Error("Task failed"))).not.toThrow();
      expect(mockPort.postMessage).toHaveBeenCalled();
      expect(db.failDownload).toHaveBeenCalledWith("item1");
    });

    it("should queue only the bounded set returned by getItemsToProcess", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["message1", "message2", "file1"]);
      db.getItem = vi.fn((id) => {
        if (id === "file1") {
          return mockItem(
            {
              kind: "file",
              source: "source1",
              uuid: "file1",
              size: 1000,
            } as ItemMetadata,
            FetchStatus.DownloadInProgress,
          );
        }

        return mockItem(
          {
            kind: "message",
            source: "source1",
            uuid: id,
          } as ItemMetadata,
          FetchStatus.Initial,
        );
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      expect(queue.messageDownloadQueue.push).toHaveBeenCalledTimes(2);
      expect(queue.fileDownloadQueue.push).toHaveBeenCalledTimes(1);
    });

    it("should not throw if terminallyFailItem throws in task_failed handler", () => {
      const db = createMockDB();
      db.terminallyFailItem = vi.fn(() => {
        throw new Error("terminallyFailItem failed");
      });

      const queue = new TaskQueue(db);

      expect(() => {
        queue.messageDownloadQueue.emit(
          "task_failed",
          "item1",
          new Error("boom"),
        );
      }).not.toThrow();

      expect(db.terminallyFailItem).toHaveBeenCalledWith("item1");
    });

    it("should not throw if postMessage throws in task_failed handler", () => {
      const db = createMockDB();
      db.getItem = vi.fn(() =>
        mockItem(
          { kind: "message", source: "source1", uuid: "item1" } as ItemMetadata,
          FetchStatus.FailedTerminal,
        ),
      );

      const mockPort = {
        postMessage: vi.fn(() => {
          throw new Error("postMessage failed");
        }),
      } as unknown as WorkerMessagePort;

      const queue = new TaskQueue(db, mockPort);

      expect(() => {
        queue.messageDownloadQueue.emit(
          "task_failed",
          "item1",
          new Error("boom"),
        );
      }).not.toThrow();

      expect(db.terminallyFailItem).toHaveBeenCalledWith("item1");
      expect(mockPort.postMessage).toHaveBeenCalled();
    });
  });

  describe("Queue Refill", () => {
    it("should not enqueue download items when unauthed", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["msg1", "file1"]);
      db.getItem = vi.fn((id) => {
        if (id === "file1") {
          return mockItem(
            {
              kind: "file",
              source: "s1",
              uuid: "file1",
              size: 1000,
            } as ItemMetadata,
            FetchStatus.DownloadInProgress,
          );
        }
        return mockItem(
          { kind: "message", source: "s1", uuid: id } as ItemMetadata,
          FetchStatus.Initial,
        );
      });

      // authToken is null: we are unauthed
      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");

      // Trigger a refill via a completed task event
      queue.messageDownloadQueue.emit("task_finish", "prev-msg", {});

      expect(queue.messageDownloadQueue.push).not.toHaveBeenCalled();
      expect(queue.fileDownloadQueue.push).not.toHaveBeenCalled();
    });

    it("should enqueue decrypt items when unauthed", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => ["msgDecrypt", "fileDecrypt"]);
      db.getItem = vi.fn((id) => {
        if (id === "fileDecrypt") {
          return mockItem(
            {
              kind: "file",
              source: "s1",
              uuid: "fileDecrypt",
              size: 1000,
            } as ItemMetadata,
            FetchStatus.DecryptionInProgress,
          );
        }
        return mockItem(
          { kind: "message", source: "s1", uuid: id } as ItemMetadata,
          FetchStatus.DecryptionInProgress,
        );
      });

      // authToken is null: we are unauthed
      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageDecryptQueue, "push");
      vi.spyOn(queue.fileDecryptQueue, "push");
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");

      // Trigger a refill via a completed task event
      queue.messageDecryptQueue.emit("task_finish", "prev-msg", {});

      // Decryption items should still be enqueued
      expect(queue.messageDecryptQueue.push).toHaveBeenCalledWith(
        { id: "msgDecrypt" },
        expect.any(Function),
      );
      expect(queue.fileDecryptQueue.push).toHaveBeenCalledWith(
        { id: "fileDecrypt" },
        expect.any(Function),
      );
      // Download queues untouched
      expect(queue.messageDownloadQueue.push).not.toHaveBeenCalled();
      expect(queue.fileDownloadQueue.push).not.toHaveBeenCalled();
    });

    it("should refill queues after a message download task finishes", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.messageDownloadQueue.emit("task_finish", "item1", {});

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
    });

    it("should refill queues after a message decrypt task finishes", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.messageDecryptQueue.emit("task_finish", "item1", {});

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
    });

    it("should refill queues after a file download task finishes", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.fileDownloadQueue.emit("task_finish", "file1", {});

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
    });

    it("should refill queues after a file decrypt task finishes", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.fileDecryptQueue.emit("task_finish", "file1", {});

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
    });

    it("should refill queues after a task terminally fails", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.messageDownloadQueue.emit(
        "task_failed",
        "item1",
        new Error("boom"),
      );

      expect(db.getItemsToProcess).toHaveBeenCalledWith({
        messageLimit: 25,
        fileLimit: 2,
      });
    });

    it("should enqueue new items returned by refill after download completes", () => {
      const db = createMockDB();
      // First call: initial queueFetches; second: refill from messageDownloadQueue finish
      db.getItemsToProcess = vi
        .fn()
        .mockReturnValueOnce(["msg2", "msg3"])
        .mockReturnValueOnce([]);
      db.getItem = vi.fn((id) =>
        mockItem(
          { kind: "message", source: "source1", uuid: id } as ItemMetadata,
          FetchStatus.Initial,
        ),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      vi.spyOn(queue.messageDownloadQueue, "push");

      queue.messageDownloadQueue.emit("task_finish", "msg1", {});

      expect(queue.messageDownloadQueue.push).toHaveBeenCalledTimes(2);
      expect(queue.messageDownloadQueue.push).toHaveBeenCalledWith(
        { id: "msg2" },
        expect.any(Function),
      );
      expect(queue.messageDownloadQueue.push).toHaveBeenCalledWith(
        { id: "msg3" },
        expect.any(Function),
      );
    });

    it("should route DecryptionInProgress items from refill to decrypt queues", () => {
      const db = createMockDB();
      // After a download finishes, the item moves to DecryptionInProgress.
      // The refill should push it to the decrypt queue.
      db.getItemsToProcess = vi
        .fn()
        .mockReturnValueOnce(["msg1"])
        .mockReturnValueOnce([]);
      db.getItem = vi.fn(() =>
        mockItem(
          { kind: "message", source: "s1", uuid: "msg1" } as ItemMetadata,
          FetchStatus.DecryptionInProgress,
        ),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.messageDecryptQueue, "push");

      queue.messageDownloadQueue.emit("task_finish", "msg1", {});

      // Item is now in decrypt phase — goes to messageDecryptQueue
      expect(queue.messageDecryptQueue.push).toHaveBeenCalledWith(
        { id: "msg1" },
        expect.any(Function),
      );
      expect(queue.messageDownloadQueue.push).not.toHaveBeenCalled();
    });

    it("should stop refilling when database returns no more items", () => {
      const db = createMockDB();
      db.getItemsToProcess = vi.fn(() => []);
      db.getItem = vi.fn(() => null);

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      vi.spyOn(queue.messageDownloadQueue, "push");
      vi.spyOn(queue.fileDownloadQueue, "push");

      queue.fileDownloadQueue.emit("task_finish", "file1", {});

      expect(queue.messageDownloadQueue.push).not.toHaveBeenCalled();
      expect(queue.fileDownloadQueue.push).not.toHaveBeenCalled();
    });
  });

  describe("Abort Downloads for Deleted Sources", () => {
    it("should abort active downloads for a given source", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 1000,
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      let rejectProxy: (reason: unknown) => void;
      mockProxyStreamRequest.mockReturnValue(
        new Promise((_resolve, reject) => {
          rejectProxy = reject;
        }),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      const processPromise = queue.processDownload({ id: "file1" }, db);

      await new Promise((r) => setTimeout(r, 10));

      queue.abortSourceFetch("source1");

      rejectProxy!(new Error("AbortError: The operation was aborted"));

      await expect(processPromise).resolves.toBeUndefined();
    });

    it("should not abort downloads for unrelated sources", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedContent = Buffer.from("encrypted");
      mockReadStreamFor(encryptedContent);
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedContent),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      // Abort for a different source
      queue.abortSourceFetch("source2");

      // Download should still complete normally
      await queue.processDownload({ id: "msg1" }, db);
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
    });

    it("should pass abort signal to proxyStreamRequest", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted");
      mockReadStreamFor(encryptedBuffer);
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.anything(),
        expect.anything(),
        0,
        expect.any(AbortSignal),
        expect.any(Number),
        expect.any(Function),
      );
    });

    it("should clean up activeDownloads entry after download completes", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted");
      mockReadStreamFor(encryptedBuffer);
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      // Aborting now should be a no-op
      queue.abortSourceFetch("source1");
    });
  });

  describe("Mid-flight Deletion Races", () => {
    it("should skip decrypt-phase transition if item is deleted after download", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      // First getItem: processable → download proceeds
      // Second getItem (re-check after download): ScheduledDeletion → skip transition
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
        );

      const encryptedBuffer = Buffer.from("encrypted");
      mockReadStreamFor(encryptedBuffer);
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      // Download happened but decrypt phase was not entered
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should drop decryption result if item is deleted during message decryption", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      // processDecrypt re-check: deleted after decryptMessage runs
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
        )
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
        );

      const encryptedBuffer = Buffer.from("encrypted");
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);
      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: "decrypted plaintext",
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      expect(mockCrypto.decryptMessage).toHaveBeenCalled();
      expect(db.completePlaintextItem).not.toHaveBeenCalled();
    });

    it("should drop decryption result if item is deleted during file decryption", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 1000,
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.DecryptionInProgress, 0),
        )
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
        );

      mockCrypto.decryptFile.mockResolvedValue({
        finalPath: "/tmp/decrypted/file.txt",
        doubleEncryptedKeyFingerprint: null,
      });

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "file1" }, db);

      expect(mockCrypto.decryptFile).toHaveBeenCalled();
      expect(db.completeFileItem).not.toHaveBeenCalled();
    });

    it("should drop retry decryption result if item is deleted during retry", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
        )
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
        );

      mockCrypto.decryptMessage.mockResolvedValue({
        plaintext: "decrypted plaintext",
        doubleEncryptedKeyFingerprint: null,
      });
      fs.promises.readFile = vi
        .fn()
        .mockResolvedValue(Buffer.from("encrypted"));

      const queue = new TaskQueue(db);
      await queue.processDecrypt({ id: "msg1" }, db);

      expect(mockCrypto.decryptMessage).toHaveBeenCalled();
      expect(db.completePlaintextItem).not.toHaveBeenCalled();
    });

    it("should not proceed to download if item is in non-processable state at start", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.ScheduledDeletion, 0),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });
  });

  describe("Download Retry and Cancel Scenarios", () => {
    it("should successfully retry a failed download when status is reset to DownloadInProgress with progress=0", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 150000000, // 150MB file
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.DownloadInProgress, 0),
        );

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 100000000,
        error: new Error("Connection lost"),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      await expect(queue.processDownload({ id: "file1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.failDownload).toHaveBeenCalledWith("file1");

      vi.clearAllMocks();

      db.getItem = vi
        .fn()
        .mockReturnValue(mockItem(metadata, FetchStatus.DownloadInProgress, 0));

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 150000000,
        sha256sum: FILE_ETAG,
      });

      await queue.processDownload({ id: "file1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/file1/download",
        }),
        expect.anything(),
        0,
        expect.any(AbortSignal),
        expect.any(Number),
        expect.any(Function),
      );

      expect(db.setDecryptionInProgress).toHaveBeenCalled();
    });

    it("should resume from actual file size on disk, not DB progress", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 100000000,
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValue(
          mockItem(metadata, FetchStatus.DownloadInProgress, 60000000),
        );

      (fs.promises.stat as ReturnType<typeof vi.fn>).mockResolvedValue({
        size: 50000000,
      });

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 50000000,
        sha256sum: FILE_ETAG,
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "file1" }, db);

      // Should resume from actual file size (50MB), not DB value (60MB)
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.anything(),
        expect.anything(),
        50000000,
        expect.any(AbortSignal),
        expect.any(Number),
        expect.any(Function),
      );
    });

    it("should start from 0 when progress > 0 but the file is missing on disk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 100000000,
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValue(
          mockItem(metadata, FetchStatus.DownloadInProgress, 50000000),
        );

      const enoentError = Object.assign(new Error("ENOENT"), {
        code: "ENOENT",
      });
      (fs.promises.stat as ReturnType<typeof vi.fn>)
        .mockRejectedValueOnce(enoentError)
        .mockResolvedValue({ size: 100000000 });

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100000000,
        sha256sum: FILE_ETAG,
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "file1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.anything(),
        expect.anything(),
        0,
        expect.any(AbortSignal),
        expect.any(Number),
        expect.any(Function),
      );
    });

    it("should not call failDownload or transition to decrypt when a download is cancelled", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 200000000,
        uuid: "file1",
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValue(mockItem(metadata, FetchStatus.DownloadInProgress, 0));

      mockProxyStreamRequest.mockImplementation(
        async (_req, _writer, _offset, _abortSignal: AbortSignal) => {
          queue.cancelDownload("file1");
          return {
            complete: false,
            bytesWritten: 10000000,
            error: new Error("aborted"),
          } as ProxyStreamResponse;
        },
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "file1" }, db);

      expect(db.failDownload).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
      expect(mockCrypto.decryptFile).not.toHaveBeenCalled();
    });
  });

  describe("ETag checksum verification", () => {
    it("should succeed when message ETag matches downloaded content", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted message data");
      mockReadStreamFor(encryptedBuffer);

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: encryptedBuffer.length,
        sha256sum: etagFor(encryptedBuffer),
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "msg1" }, db);

      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(db.failDownload).not.toHaveBeenCalled();
    });

    it("should fail terminally when message ETag does not match", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const encryptedBuffer = Buffer.from("encrypted message data");
      mockReadStreamFor(encryptedBuffer);

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: encryptedBuffer.length,
        sha256sum:
          "sha256:0000000000000000000000000000000000000000000000000000000000000000",
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "ETag checksum mismatch",
      );

      expect(db.terminallyFailItem).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should succeed when file ETag matches downloaded content", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 1000000,
        sha256sum: FILE_ETAG,
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await queue.processDownload({ id: "file1" }, db);

      const expectedDownloadPath = path.join(
        os.tmpdir(),
        "download",
        "source1",
        "file1",
        "encrypted.gpg",
      );
      expect(fs.createReadStream).toHaveBeenCalledWith(expectedDownloadPath);
      expect(db.setDecryptionInProgress).toHaveBeenCalled();
      expect(db.failDownload).not.toHaveBeenCalled();
    });

    it("should fail terminally when file ETag does not match", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 1000000,
        sha256sum:
          "sha256:0000000000000000000000000000000000000000000000000000000000000000",
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await expect(queue.processDownload({ id: "file1" }, db)).rejects.toThrow(
        "ETag checksum mismatch",
      );

      expect(db.terminallyFailItem).toHaveBeenCalledWith("file1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should fail terminally when ETag is missing", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        // no sha256sum
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "Missing ETag checksum",
      );

      expect(db.terminallyFailItem).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should fail terminally when ETag has an invalid or unsupported format", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
        sha256sum: "md5:d8e8fca2dc0f896fd7cb4cb0031ba249",
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";
      await expect(queue.processDownload({ id: "msg1" }, db)).rejects.toThrow(
        "Invalid or unsupported ETag format",
      );

      expect(db.terminallyFailItem).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });
  });

  describe("Large Backlog Regression", () => {
    it("refill should drain a large backlog by re-querying after each task completes", () => {
      const db = createMockDB();

      db.getItemsToProcess = vi
        .fn()
        .mockReturnValueOnce(["msg1", "msg2", "msg3"])
        .mockReturnValueOnce(["msg4", "msg5"])
        .mockReturnValueOnce([]);

      db.getItem = vi.fn((uuid: string) =>
        mockItem(
          {
            kind: "message",
            source: "source1",
            size: 100,
            uuid,
          } as ItemMetadata,
          FetchStatus.Initial,
          0,
        ),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.queueFetches({ authToken: "test-token" });
      expect(db.getItemsToProcess).toHaveBeenCalledTimes(1);

      queue.messageDownloadQueue.emit("task_finish", "msg1", {});
      expect(db.getItemsToProcess).toHaveBeenCalledTimes(2);

      queue.messageDownloadQueue.emit("task_finish", "msg4", {});
      expect(db.getItemsToProcess).toHaveBeenCalledTimes(3);
    });

    it("deletion during large backlog should prevent new items from being queued", () => {
      const db = createMockDB();

      db.getItemsToProcess = vi
        .fn()
        .mockReturnValueOnce(["msg1", "msg2"])
        .mockReturnValueOnce([]);

      const msg1Meta = {
        kind: "message",
        source: "source1",
        size: 100,
        uuid: "msg1",
      } as ItemMetadata;

      db.getItem = vi.fn((uuid: string) => {
        if (uuid === "msg1") {
          return mockItem(msg1Meta, FetchStatus.ScheduledDeletion, 0);
        }
        return mockItem(
          {
            kind: "message",
            source: "source1",
            size: 100,
            uuid,
          } as ItemMetadata,
          FetchStatus.Initial,
          0,
        );
      });

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      queue.queueFetches({ authToken: "test-token" });
      queue.messageDownloadQueue.emit("task_finish", "msg1", {});

      expect(db.getItemsToProcess).toHaveBeenCalledTimes(2);
    });

    it("abort should cancel all active downloads for a deleted source across a backlog", async () => {
      const db = createMockDB();

      const fileMeta = (uuid: string) =>
        ({
          kind: "file",
          source: "source1",
          size: 10000,
          uuid,
        }) as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(
          mockItem(fileMeta("file1"), FetchStatus.Initial, 0),
        )
        .mockReturnValueOnce(
          mockItem(fileMeta("file2"), FetchStatus.Initial, 0),
        );

      const rejects: Array<(reason: unknown) => void> = [];
      mockProxyStreamRequest.mockImplementation(
        () =>
          new Promise((_resolve, reject) => {
            rejects.push(reject);
          }),
      );

      const queue = new TaskQueue(db);
      queue.authToken = "test-token";

      const p1 = queue.processDownload({ id: "file1" }, db);
      const p2 = queue.processDownload({ id: "file2" }, db);

      await new Promise((r) => setTimeout(r, 10));

      queue.abortSourceFetch("source1");

      for (const reject of rejects) {
        reject(new Error("AbortError: The operation was aborted"));
      }

      await expect(p1).resolves.toBeUndefined();
      await expect(p2).resolves.toBeUndefined();
    });
  });
});
