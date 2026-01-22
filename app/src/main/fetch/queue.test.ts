import { describe, it, expect, vi, beforeEach, Mock } from "vitest";
import fs from "fs";
import os from "os";
import path from "path";
import { PassThrough } from "stream";
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
import { BufferedWriter } from "./bufferedWriter";

// Mocks
const mockProxyStreamRequest = vi.hoisted(() => {
  return vi.fn();
});
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

// Mock fs for file operations during decryption failure scenarios
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
  },
  existsSync: vi.fn(() => true),
  realpathSync: vi.fn((path) => path),
  mkdtempSync: vi.fn((prefix) => prefix + "XXXXXX"),
  mkdirSync: vi.fn(),
  rmSync: vi.fn(),
}));

// Helper to create mock DB with specific methods
function createMockDB() {
  return {
    getItemsToProcess: vi.fn(),
    getItem: vi.fn(),
    getSource: vi.fn(),
    completePlaintextItem: vi.fn(),
    completeFileItem: vi.fn(),
    setDownloadInProgress: vi.fn(),
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
  fetch_progress?: number,
): Item {
  return {
    uuid: "id",
    data: metadata,
    fetch_status,
    fetch_progress,
  };
}

describe("TaskQueue - Two-Phase Download and Decryption", () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockCrypto.decryptMessage.mockReset();
    mockCrypto.decryptFile.mockReset();
  });

  describe("Message Processing", () => {
    it("should download and decrypt a message successfully on first attempt", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      // Mock: item is in Initial status
      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      // Mock successful download
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      // Mock successful decryption
      const encryptedBuffer = Buffer.from("encrypted message data");
      const decryptedContent = "decrypted message content";
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);

      const queue = new TaskQueue(db);
      await queue.process({ id: "msg1" }, db);

      // Verify download phase
      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/msg1/download",
        }),
        expect.any(BufferedWriter),
        0,
        undefined, // abortSignal
        20000, // timeout
        expect.any(Function), // onProgress
      );

      // Verify decryption phase
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(mockCrypto.decryptMessage).toHaveBeenCalledWith(encryptedBuffer);
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
      );
    });

    it("should download successfully but fail decryption, save to disk, and retry decryption only", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      // First attempt: Initial status
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
        );

      // Mock successful download
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      const encryptedBuffer = Buffer.from("encrypted message data");
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );

      // Mock decryption failure on first attempt
      mockCrypto.decryptMessage.mockRejectedValueOnce(
        new CryptoError("Decryption failed"),
      );

      const queue = new TaskQueue(db);

      // First attempt - should fail decryption and save to disk
      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        `Decryption failed`,
      );

      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(db.failDecryption).toHaveBeenCalledWith("msg1");

      // Verify encrypted data was saved to disk for retry
      expect(fs.promises.mkdir).toHaveBeenCalled();
      expect(fs.promises.writeFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
        encryptedBuffer,
      );

      // Second attempt - retry from FailedDecryptionRetryable status
      // Mock successful decryption this time
      const decryptedContent = "decrypted message content";
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);

      await queue.process({ id: "msg1" }, db);

      // Should only do decryption phase (no download)
      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(1); // Only called once (first attempt)
      expect(fs.promises.readFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
      );

      // Should clean up the file after successful decryption
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });

    it("should fail download, retry download and decryption successfully", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      // First attempt: Initial status, Second attempt: FailedDownloadRetryable
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDownloadRetryable, 50),
        );

      const queue = new TaskQueue(db);

      // First attempt - download fails
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 50,
        error: new Error("Network error"),
      });

      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1", 50); // Progress update
      expect(db.failDownload).toHaveBeenCalledWith("msg1");

      // Second attempt - download and decrypt successfully
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100,
      });

      const encryptedBuffer = Buffer.from("encrypted message data");
      const decryptedContent = "decrypted message content";
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);

      await queue.process({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(2);
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
      );
    });
  });

  describe("Reply Processing", () => {
    it("should download and decrypt a reply successfully on first attempt", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "reply",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      const encryptedBuffer = Buffer.from("encrypted reply data");
      const decryptedContent = "decrypted reply content";
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);

      const queue = new TaskQueue(db);
      await queue.process({ id: "reply1" }, db);

      // Verify reply uses correct API endpoint
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/replies/reply1/download",
        }),
        expect.any(BufferedWriter),
        0,
        undefined, // abortSignal
        20000, // timeout
        expect.any(Function), // onProgress
      );

      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "reply1",
        decryptedContent,
      );
    });

    it("should download successfully but fail decryption, save to disk, and retry decryption only", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "reply",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
        );

      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      const encryptedBuffer = Buffer.from("encrypted reply data");
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );

      // First attempt - decryption fails
      mockCrypto.decryptMessage.mockRejectedValueOnce(
        new CryptoError("Decryption failed"),
      );

      const queue = new TaskQueue(db);

      // Should fail decryption and save to disk
      await expect(queue.process({ id: "reply1" }, db)).rejects.toThrow(
        `Decryption failed`,
      );

      expect(db.failDecryption).toHaveBeenCalledWith("reply1");
      expect(fs.promises.writeFile).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
        encryptedBuffer,
      );

      // Second attempt - successful decryption from disk
      const decryptedContent = "decrypted reply content";
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);
      fs.promises.readFile = vi.fn().mockResolvedValue(encryptedBuffer);

      await queue.process({ id: "reply1" }, db);

      expect(fs.promises.readFile).toHaveBeenCalled();
      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "reply1",
        decryptedContent,
      );
      expect(fs.promises.unlink).toHaveBeenCalled();
    });

    it("should fail download, retry download and decryption successfully", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "reply",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDownloadRetryable, 30),
        );

      const queue = new TaskQueue(db);

      // First attempt - download fails
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 30,
      });

      await expect(queue.process({ id: "reply1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );
      expect(db.failDownload).toHaveBeenCalledWith("reply1");

      // Second attempt - success
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100,
      });

      const encryptedBuffer = Buffer.from("encrypted reply data");
      const decryptedContent = "decrypted reply content";
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);

      await queue.process({ id: "reply1" }, db);

      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "reply1",
        decryptedContent,
      );
    });
  });

  describe("File Processing", () => {
    it("should download and decrypt a file successfully on first attempt", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-1",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      // Mock successful download
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      // Mock successful decryption
      mockCrypto.decryptFile.mockResolvedValue(
        "/securedrop/source1/plaintext.txt",
      );

      const queue = new TaskQueue(db);
      await queue.process({ id: "msg1" }, db);

      // Verify download phase
      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/msg1/download",
        }),
        expect.any(PassThrough),
        0,
        undefined, // abortSignal
        55000, // timeout
        expect.any(Function), // onProgress
      );

      // Verify decryption phase
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
      );
      expect(db.completeFileItem).toHaveBeenCalledWith(
        "msg1",
        "/securedrop/source1/plaintext.txt",
        expect.any(Number),
      );
    });

    it("should send throttled progress updates and update db for each chunk", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-progress",
      } as ItemMetadata;

      // Always return an item in Initial state for simplicity
      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));
      db.getSource = vi.fn(() => ({}) as never);

      // Mock crypto decryption success
      mockCrypto.decryptFile.mockResolvedValue(
        "/securedrop/source1/plaintext.txt",
      );

      // Mock Date.now to control throttling intervals
      const nowSpy = vi
        .spyOn(Date, "now")
        .mockReturnValueOnce(200) // first progress -> postMessage
        .mockReturnValueOnce(250) // within throttle window -> no postMessage
        .mockReturnValueOnce(500) // outside throttle window -> second postMessage
        .mockReturnValue(500); // default for any further calls

      // Capture onProgress and simulate chunked progress
      mockProxyStreamRequest.mockImplementation(
        async (_req, _writer, _offset, _abort, _timeout, onProgress) => {
          onProgress?.(10);
          onProgress?.(20);
          onProgress?.(30);
          return { complete: true, bytesWritten: 30 } as ProxyStreamResponse;
        },
      );

      const mockPort = { postMessage: vi.fn() } as unknown as WorkerMessagePort;
      const queue = new TaskQueue(db, mockPort);

      await queue.process({ id: "file-uuid-progress" }, db);

      // First call is the initial setDownloadInProgress, subsequent calls are from onProgress
      const setDownloadMock = db.setDownloadInProgress as unknown as Mock;
      const progressCalls = setDownloadMock.mock.calls.slice(1);
      expect(progressCalls.map((call) => call[1])).toEqual([10, 20, 30]);

      // One throttled progress post plus source update and final item update
      expect(mockPort.postMessage).toHaveBeenCalledTimes(3);
      expect(db.getSource).toHaveBeenCalledTimes(1);

      nowSpy.mockRestore();
    });

    it("should download successfully but fail decryption, and retry decryption only", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-2",
        size: 1000000,
      } as ItemMetadata;

      // First attempt: Initial status, Second attempt: FailedDecryptionRetryable
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
        );

      // Mock successful download
      mockProxyStreamRequest.mockResolvedValue({
        complete: true,
        bytesWritten: 100,
      });

      // Mock decryption failure on first attempt
      mockCrypto.decryptFile.mockRejectedValueOnce(
        new CryptoError("Decryption failed"),
      );

      const queue = new TaskQueue(db);

      // First attempt - should fail decryption
      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        `Decryption failed`,
      );

      // Verify download was saved to disk
      expect(fs.promises.mkdir).toHaveBeenCalled();
      expect(fs.createWriteStream).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );

      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.setDecryptionInProgress).toHaveBeenCalledWith("msg1");
      expect(db.failDecryption).toHaveBeenCalledWith("msg1");

      // Second attempt - retry from FailedDecryptionRetryable status
      // Mock successful decryption this time
      mockCrypto.decryptFile.mockResolvedValue(
        "/securedrop/source1/plaintext.txt",
      );

      await queue.process({ id: "msg1" }, db);

      // Should only do decryption phase (no download)
      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(1); // Only called once (first attempt)
      expect(db.completeFileItem).toHaveBeenCalledWith(
        "msg1",
        "/securedrop/source1/plaintext.txt",
        expect.any(Number),
      );
      expect(fs.promises.unlink).toHaveBeenCalledWith(
        expect.stringContaining("/encrypted.gpg"),
      );
    });

    it("should fail download, retry download and decryption successfully", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        uuid: "file-uuid-3",
        size: 1000000,
      } as ItemMetadata;

      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0))
        .mockReturnValueOnce(
          mockItem(metadata, FetchStatus.FailedDownloadRetryable, 30),
        );

      const queue = new TaskQueue(db);

      // First attempt - download fails
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 50,
        error: new Error("Network error"),
      });

      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1");
      expect(db.setDownloadInProgress).toHaveBeenCalledWith("msg1", 50); // Progress update
      expect(db.failDownload).toHaveBeenCalledWith("msg1");

      // Second attempt - download and decrypt successfully
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 100,
      });

      mockCrypto.decryptFile.mockResolvedValue(
        "/securedrop/source1/plaintext.txt",
      );

      await queue.process({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).toHaveBeenCalledTimes(2);
      expect(db.completeFileItem).toHaveBeenCalledWith(
        "msg1",
        "/securedrop/source1/plaintext.txt",
        expect.any(Number),
      );
    });
  });

  describe("Edge Cases and Error Handling", () => {
    it("should skip items that are already complete", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Complete, 0));

      const queue = new TaskQueue(db);
      await queue.process({ id: "msg1" }, db);

      // Should not perform any operations
      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
      expect(db.setDownloadInProgress).not.toHaveBeenCalled();
      expect(db.setDecryptionInProgress).not.toHaveBeenCalled();
    });

    it("should skip items that are terminally failed", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.FailedTerminal, 0),
      );

      const queue = new TaskQueue(db);
      await queue.process({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
    });

    it("should skip items that are paused", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Paused, 0));

      const queue = new TaskQueue(db);
      await queue.process({ id: "msg1" }, db);

      expect(mockProxyStreamRequest).not.toHaveBeenCalled();
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

      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        "Received error from server with status 500",
      );

      expect(db.failDownload).toHaveBeenCalledWith("msg1");
    });

    it("should handle file read errors during decryption retry", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 1000,
      } as ItemMetadata;

      db.getItem = vi.fn(() =>
        mockItem(metadata, FetchStatus.FailedDecryptionRetryable, 0),
      );

      // Mock file read error
      fs.promises.readFile = vi
        .fn()
        .mockRejectedValue(new Error("File not found"));

      const queue = new TaskQueue(db);

      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        "Failed to load encrypted data from disk",
      );

      expect(db.failDecryption).toHaveBeenCalledWith("msg1");
    });

    it("should handle unsupported item kinds", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "unknown",
        source: "source1",
      } as unknown as ItemMetadata;

      db.getItem = vi.fn(() => mockItem(metadata, FetchStatus.Initial, 0));

      const queue = new TaskQueue(db);

      await expect(queue.process({ id: "item1" }, db)).rejects.toThrow(
        "Unsupported item kind: unknown",
      );
    });
  });

  describe("Queue Integration", () => {
    it("should queue messages to messageQueue and files to fileQueue", () => {
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
            FetchStatus.Initial,
          );
        }
        return null;
      });

      const queue = new TaskQueue(db);
      vi.spyOn(queue.messageQueue, "push");
      vi.spyOn(queue.fileQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      expect(db.getItemsToProcess).toHaveBeenCalled();
      // 2 messages/replies should go to messageQueue
      expect(queue.messageQueue.push).toHaveBeenCalledTimes(2);
      // 1 file should go to fileQueue
      expect(queue.fileQueue.push).toHaveBeenCalledTimes(1);
      expect(queue.authToken).toBe("test-token");
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
      vi.spyOn(queue.messageQueue, "push");

      queue.queueFetches({ authToken: "test-token" });

      // Simulate the error callback that gets passed to queue.push
      const pushCall = vi.mocked(queue.messageQueue.push).mock.calls[0];
      expect(pushCall).toBeDefined();
      expect(pushCall[1]).toBeTypeOf("function");

      // Call the error callback with an error
      const errorCallback = pushCall[1] as (
        err: Error | null,
        result?: unknown,
      ) => void;
      errorCallback(new Error("Task failed"));

      expect(db.failDownload).toHaveBeenCalledWith("item1");
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

      // First attempt: download fails partway through
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 100000000, // 100MB downloaded before failure
        error: new Error("Connection lost"),
      });

      const queue = new TaskQueue(db);

      // First attempt should fail
      await expect(queue.process({ id: "file1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.failDownload).toHaveBeenCalledWith("file1");

      // Simulate the UI clicking "Retry" - status reset to DownloadInProgress with progress=0
      // (This would be done by updateFetchStatus in index.ts which resets progress)
      vi.clearAllMocks();

      db.getItem = vi.fn().mockReturnValue(
        // Progress is now 0 because updateFetchStatus reset it
        mockItem(metadata, FetchStatus.DownloadInProgress, 0),
      );

      // Second attempt should succeed
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 150000000,
        sha256sum: "abc123",
      });

      mockCrypto.decryptFile.mockResolvedValue({
        decryptedFilePath: "/tmp/decrypted/file.txt",
        decryptedSize: 145000000,
      });

      await queue.process({ id: "file1" }, db);

      // Verify it started fresh from offset 0, not from the old progress
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/file1/download",
        }),
        expect.anything(),
        0, // Should start from 0, not 100000000
        undefined, // abortSignal
        expect.any(Number), // timeout
        expect.any(Function), // onProgress
      );

      expect(db.completeFileItem).toHaveBeenCalled();
    });

    it("should start fresh download after cancel (status reset to Initial)", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "file",
        source: "source1",
        size: 200000000, // 200MB file
        uuid: "file1",
      } as ItemMetadata;

      // First attempt: download fails
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 50000000, // 50MB downloaded
        error: new Error("Timeout"),
      });

      const queue = new TaskQueue(db);

      await expect(queue.process({ id: "file1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.failDownload).toHaveBeenCalledWith("file1");

      // Simulate user clicking "Cancel" - status reset to Initial with progress=0
      vi.clearAllMocks();

      db.getItem = vi.fn().mockReturnValue(
        // Progress is 0 because updateFetchStatus reset it when going to Initial
        mockItem(metadata, FetchStatus.Initial, 0),
      );

      // Now user clicks download again
      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 200000000,
        sha256sum: "def456",
      });

      mockCrypto.decryptFile.mockResolvedValue({
        decryptedFilePath: "/tmp/decrypted/file.txt",
        decryptedSize: 195000000,
      });

      await queue.process({ id: "file1" }, db);

      // Should start from 0
      expect(mockProxyStreamRequest).toHaveBeenCalledWith(
        expect.objectContaining({
          path_query: "/api/v1/sources/source1/submissions/file1/download",
        }),
        expect.anything(),
        0, // Fresh start from 0
        undefined, // abortSignal
        expect.any(Number), //timeout
        expect.any(Function), // onProgress
      );

      expect(db.completeFileItem).toHaveBeenCalled();
    });

    it("should fail gracefully and allow retry for message downloads", async () => {
      const db = createMockDB();
      const metadata = {
        kind: "message",
        source: "source1",
        size: 5000,
      } as ItemMetadata;

      // First attempt fails
      db.getItem = vi
        .fn()
        .mockReturnValueOnce(mockItem(metadata, FetchStatus.Initial, 0));

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: false,
        bytesWritten: 2500,
        error: new Error("Network error"),
      });

      const queue = new TaskQueue(db);

      await expect(queue.process({ id: "msg1" }, db)).rejects.toThrow(
        "Unable to complete stream download",
      );

      expect(db.failDownload).toHaveBeenCalledWith("msg1");

      // Retry after status reset
      vi.clearAllMocks();

      db.getItem = vi
        .fn()
        .mockReturnValue(mockItem(metadata, FetchStatus.DownloadInProgress, 0));

      mockProxyStreamRequest.mockResolvedValueOnce({
        complete: true,
        bytesWritten: 5000,
      });

      const encryptedBuffer = Buffer.from("encrypted message");
      const decryptedContent = "Hello, world!";
      vi.spyOn(BufferedWriter.prototype, "getBuffer").mockReturnValue(
        encryptedBuffer,
      );
      mockCrypto.decryptMessage.mockResolvedValue(decryptedContent);

      await queue.process({ id: "msg1" }, db);

      expect(db.completePlaintextItem).toHaveBeenCalledWith(
        "msg1",
        decryptedContent,
      );
    });
  });
});
