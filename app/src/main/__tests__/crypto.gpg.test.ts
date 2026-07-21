import {
  describe,
  it,
  expect,
  beforeAll,
  afterAll,
  beforeEach,
  afterEach,
} from "vitest";
import * as path from "path";
import * as fs from "fs";
import * as os from "os";
import * as openpgp from "openpgp";
import { execFileSync, execSync, spawn } from "child_process";
import { EventEmitter } from "events";
import { PassThrough, Readable, Writable } from "stream";
import { pipeline } from "stream/promises";
import { createGzip, gzipSync } from "zlib";
import {
  createDecryptedByteLimit,
  Crypto,
  CryptoError,
  encryptMessage,
  MAX_DECRYPTED_BYTES,
  MAX_DECRYPTED_GZIP_BYTES,
  MAX_GPG_STDERR_BYTES,
} from "../crypto";
import {
  createGpgTestEnvironment,
  createTestEncryptedFile,
  verifyGpgAvailable,
  loadTestKeys,
  type GpgTestEnvironment,
} from "./setup-gpg-tests";
import { PathBuilder, Storage } from "../storage";

vi.mock("child_process", { spy: true });

// Verify GPG is available - fail tests if not
const isGpgAvailable = verifyGpgAvailable();

interface EncryptedFileFixture {
  cleanup: () => void;
  filePath: string;
}

function* largeByteChunks(
  plaintextBytes: number,
  fillByte = 0x41,
): Generator<Buffer> {
  const chunk = Buffer.alloc(1024 * 1024, fillByte);
  for (let bytes = 0; bytes < plaintextBytes; bytes += chunk.length) {
    yield chunk.subarray(0, Math.min(chunk.length, plaintextBytes - bytes));
  }
}

async function createLargeEncryptedFile(
  plaintextBytes: number,
  recipientKeyId: string,
  gpgHomedir: string,
): Promise<EncryptedFileFixture> {
  const tempDirectory = fs.mkdtempSync(
    path.join(os.tmpdir(), "crypto-large-file-test-"),
  );
  const gzipPath = path.join(tempDirectory, "large-fixture.gz");
  const encryptedPath = path.join(tempDirectory, "large-fixture.gpg");

  await pipeline(
    Readable.from(largeByteChunks(plaintextBytes)),
    createGzip({ level: 9 }),
    fs.createWriteStream(gzipPath),
  );
  execFileSync("gpg", [
    "--homedir",
    gpgHomedir,
    "--batch",
    "--trust-model",
    "always",
    "--encrypt",
    "-r",
    recipientKeyId,
    "--output",
    encryptedPath,
    gzipPath,
  ]);
  return {
    cleanup: () => fs.rmSync(tempDirectory, { force: true, recursive: true }),
    filePath: encryptedPath,
  };
}

async function createStoredOpenPgpFile(
  plaintextBytes: number,
  gpgHomedir: string,
): Promise<EncryptedFileFixture> {
  const tempDirectory = fs.mkdtempSync(
    path.join(os.tmpdir(), "crypto-openpgp-file-test-"),
  );
  const plainPath = path.join(tempDirectory, "stored-packet-plain.bin");
  const packetPath = path.join(tempDirectory, "stored-packet.asc");

  await pipeline(
    Readable.from(largeByteChunks(plaintextBytes, 0x45)),
    fs.createWriteStream(plainPath),
  );
  execFileSync("gpg", [
    "--batch",
    "--yes",
    "--no-options",
    "--homedir",
    gpgHomedir,
    "--compress-algo",
    "zlib",
    "--store",
    "--armor",
    "--output",
    packetPath,
    plainPath,
  ]);
  return {
    cleanup: () => fs.rmSync(tempDirectory, { force: true, recursive: true }),
    filePath: packetPath,
  };
}

function abortPlaintextAtSize(
  controller: AbortController,
  targetBytes: number,
): { maxBytes: () => number; stop: () => void } {
  let maxBytes = 0;
  const recordWrite = (
    stream: fs.WriteStream,
    bytes: number,
    error?: Error | null,
  ) => {
    if (!error && path.basename(String(stream.path)) === "plaintext") {
      maxBytes += bytes;
    }
    if (maxBytes >= targetBytes && !controller.signal.aborted) {
      controller.abort();
    }
  };
  const prototype = fs.WriteStream.prototype as any;
  const write = prototype._write;
  prototype._write = function (
    this: fs.WriteStream,
    chunk: Buffer,
    encoding: BufferEncoding,
    callback: (error?: Error | null) => void,
  ): void {
    write.call(this, chunk, encoding, (error?: Error | null) => {
      recordWrite(this, chunk.length, error);
      callback(error);
    });
  };
  const writev = prototype._writev;
  prototype._writev = function (
    this: fs.WriteStream,
    chunks: Array<{ chunk: Buffer; encoding: BufferEncoding }>,
    callback: (error?: Error | null) => void,
  ): void {
    writev.call(this, chunks, (error?: Error | null) => {
      const bytes = chunks.reduce(
        (total, entry) => total + entry.chunk.length,
        0,
      );
      recordWrite(this, bytes, error);
      callback(error);
    });
  };
  return {
    maxBytes: () => maxBytes,
    stop: () => {
      prototype._write = write;
      prototype._writev = writev;
    },
  };
}

describe("Crypto with Real GPG", () => {
  let gpgEnv: GpgTestEnvironment;
  let crypto: Crypto;
  let testKeyId: string;
  const storage = new Storage();
  let itemDirectory: PathBuilder;
  let testRecipients: string[];

  beforeAll(async () => {
    if (!isGpgAvailable) {
      throw new Error(
        "GPG is required but not available on this system. Please install GPG to run crypto tests.",
      );
    }

    gpgEnv = createGpgTestEnvironment();

    // Try to load and import test keys first
    const testFilesDir = path.join(__dirname, "files");
    const { publicKey, privateKey } = loadTestKeys(testFilesDir);

    if (publicKey && privateKey) {
      testRecipients = [publicKey, privateKey];
      console.log("Importing test keys from files...");
      try {
        gpgEnv.importKey(privateKey); // Import private key (contains public key too)
        const keys = gpgEnv.listKeys();
        if (keys.length > 0) {
          testKeyId = keys[0];
          console.log(`Imported test key: ${testKeyId}`);
        }
      } catch (_error) {
        console.warn("Failed to import test keys, creating new ones...");
      }
    }

    // If no test keys or import failed, create a new key
    if (!testKeyId) {
      console.log("Creating new test key...");
      testKeyId = gpgEnv.createTestKey("Test User", "test@securedrop.test");
      console.log(`Created test key: ${testKeyId}`);
    }

    expect(testKeyId).toBeTruthy();
  });

  afterAll(() => {
    gpgEnv?.cleanup();
  });

  beforeEach(() => {
    // Reset singleton and create with test homedir
    (Crypto as any).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      gpgHomedir: gpgEnv.homedir,
      submissionKeyFingerprint: "",
    });
    crypto = Crypto.getInstance()!;

    // Create fresh itemDirectory for each test
    itemDirectory = storage.createTempDir("securedrop-test-");
  });

  afterEach(() => {
    // Cleanup itemDirectory after each test
    if (itemDirectory && fs.existsSync(itemDirectory.path)) {
      fs.rmSync(itemDirectory.path, { recursive: true, force: true });
    }
  });

  describe("Message Decryption (No Gzip)", () => {
    it("should decrypt a simple text message", async () => {
      const originalMessage = "Hello, this is a secret message!";

      // Encrypt using GPG directly
      const encryptedContent = Buffer.from(
        await encryptMessage(originalMessage, testRecipients),
        "utf-8",
      );

      // Decrypt using our crypto class
      const decryptedMessage = await crypto.decryptMessage(encryptedContent);

      expect(decryptedMessage).toBe(originalMessage);
    });

    it("should decrypt a message with newlines and special characters", async () => {
      const originalMessage = `This is a multi-line message
with special characters: àáâãäåæçèéêë
and symbols: !@#$%^&*()_+-={}[]|\\:";'<>?,./`;

      const encryptedContent = Buffer.from(
        await encryptMessage(originalMessage, testRecipients),
        "utf-8",
      );

      const decryptedMessage = await crypto.decryptMessage(encryptedContent);

      expect(decryptedMessage).toBe(originalMessage);
    });

    it("should fail with invalid encrypted data", async () => {
      const invalidData = Buffer.from("This is not encrypted data");

      await expect(crypto.decryptMessage(invalidData)).rejects.toThrow(
        CryptoError,
      );
    });

    it("should handle empty message", async () => {
      const originalMessage = "";

      const encryptedContent = Buffer.from(
        await encryptMessage(originalMessage, testRecipients),
        "utf-8",
      );

      const decryptedMessage = await crypto.decryptMessage(encryptedContent);

      expect(decryptedMessage).toBe(originalMessage);
    });
  });

  describe("File Decryption (With Gzip)", () => {
    it("should decrypt and decompress a simple text file", async () => {
      const originalContent = "This is the content of a secret document.";
      const originalFilename = "secret-document.txt";

      // Create encrypted file using helper
      const { filePath, cleanup } = createTestEncryptedFile(
        originalContent,
        originalFilename,
        testKeyId,
        gpgEnv.homedir,
      );
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      const createTempDirSpy = vi
        .spyOn(storage, "createTempDir")
        .mockImplementation((prefix) => {
          const directory = createTempDir(prefix);
          operationDirectories.push(directory.path);
          return directory;
        });

      try {
        // Decrypt using our crypto class
        const result = await crypto.decryptFile(
          storage,
          itemDirectory,
          filePath,
        );

        expect(path.basename(result)).toBe(originalFilename);

        // Read the decrypted file and verify content
        const fs = await import("fs");
        const decryptedContent = fs.readFileSync(result, "utf8");
        expect(decryptedContent).toBe(originalContent);
        expect(operationDirectories).toHaveLength(1);
        expect(fs.existsSync(operationDirectories[0])).toBe(false);
      } finally {
        createTempDirSpy.mockRestore();
        cleanup();
      }
    });

    it("should handle binary file content", async () => {
      // Create binary content (simulating an image or other binary file)
      const binaryContent = Buffer.from([
        0x89,
        0x50,
        0x4e,
        0x47,
        0x0d,
        0x0a,
        0x1a,
        0x0a, // PNG signature
        ...Array(50)
          .fill(0)
          .map((_, i) => i % 256),
      ]);
      const originalFilename = "test-image.png";

      const { filePath, cleanup } = createTestEncryptedFile(
        binaryContent,
        originalFilename,
        testKeyId,
        gpgEnv.homedir,
      );

      try {
        const result = await crypto.decryptFile(
          storage,
          itemDirectory,
          filePath,
        );

        expect(path.basename(result)).toBe(originalFilename);

        // Read the decrypted file and verify binary content
        const fs = await import("fs");
        const decryptedContent = fs.readFileSync(result);

        // Compare binary data
        expect(Buffer.compare(decryptedContent, binaryContent)).toBe(0);
      } finally {
        cleanup();
      }
    });

    it("should handle file with long filename", async () => {
      const originalContent = "Content with a very long filename";
      const longFilename =
        "this-is-a-very-long-filename-that-tests-the-limits-of-filename-extraction.txt";

      const { filePath, cleanup } = createTestEncryptedFile(
        originalContent,
        longFilename,
        testKeyId,
        gpgEnv.homedir,
      );

      try {
        const result = await crypto.decryptFile(
          storage,
          itemDirectory,
          filePath,
        );

        expect(path.basename(result)).toBe(longFilename);

        const fs = await import("fs");
        const decryptedContent = fs.readFileSync(result, "utf8");
        expect(decryptedContent).toBe(originalContent);
      } finally {
        cleanup();
      }
    });

    it("should not leave plaintext when malformed gzip decompression fails", async () => {
      const fixtureDirectory = fs.mkdtempSync(
        path.join(itemDirectory.path, "encrypted-fixture-"),
      );
      const malformedGzipPath = path.join(fixtureDirectory, "malformed-output");
      const encryptedPath = `${malformedGzipPath}.gpg`;
      const plaintext = Buffer.alloc(4 * 1024 * 1024, 0x41);
      const gzipPayload = gzipSync(plaintext, { level: 9 });
      fs.writeFileSync(
        malformedGzipPath,
        gzipPayload.subarray(0, gzipPayload.length - 8),
      );
      execFileSync("gpg", [
        "--homedir",
        gpgEnv.homedir,
        "--batch",
        "--trust-model",
        "always",
        "--encrypt",
        "-r",
        testKeyId,
        "--output",
        encryptedPath,
        malformedGzipPath,
      ]);

      const finalOutputPath = itemDirectory.join("malformed-output");
      try {
        await expect(
          crypto.decryptFile(storage, itemDirectory, encryptedPath),
        ).rejects.toThrow("Failed to decompress decrypted file");

        const finalOutputExists = fs.existsSync(finalOutputPath);
        expect({
          finalOutputExists,
          finalOutputBytes: finalOutputExists
            ? fs.statSync(finalOutputPath).size
            : 0,
          itemDirectoryEntries: fs
            .readdirSync(itemDirectory.path)
            .filter((entry) => entry !== path.basename(fixtureDirectory)),
        }).toEqual({
          finalOutputExists: false,
          finalOutputBytes: 0,
          itemDirectoryEntries: [],
        });
      } finally {
        fs.rmSync(fixtureDirectory, { recursive: true, force: true });
      }
    });

    it("should fail with non-existent encrypted file", async () => {
      const nonExistentPath = "/path/that/does/not/exist.gpg";

      await expect(
        crypto.decryptFile(storage, itemDirectory, nonExistentPath),
      ).rejects.toThrow(CryptoError);
    });
  });

  describe("Key Differences: Message vs File", () => {
    it("should demonstrate message flow (no gzip)", async () => {
      const testData = "Secret message data";

      // Messages: encrypt directly, decrypt directly (no compression)
      const encryptedMessage = Buffer.from(
        await encryptMessage(testData, testRecipients),
        "utf-8",
      );

      const decryptedMessage = await crypto.decryptMessage(encryptedMessage);
      expect(decryptedMessage).toBe(testData);
    });

    it("should demonstrate file flow (with gzip)", async () => {
      const testData = "Secret file data that gets gzipped";
      const filename = "secret-file.txt";

      // Files: compress first, then encrypt; decrypt then decompress
      const { filePath, cleanup } = createTestEncryptedFile(
        testData,
        filename,
        testKeyId,
        gpgEnv.homedir,
      );

      try {
        const result = await crypto.decryptFile(
          storage,
          itemDirectory,
          filePath,
        );

        expect(path.basename(result)).toBe(filename);

        const fs = await import("fs");
        const decryptedContent = fs.readFileSync(result, "utf8");
        expect(decryptedContent).toBe(testData);
      } finally {
        cleanup();
      }
    });
  });

  describe("Performance and Reliability", () => {
    it("should handle moderately large messages efficiently", async () => {
      // Create a 50KB message
      const largeMessage = "A".repeat(50000);

      const encryptedContent = Buffer.from(
        await encryptMessage(largeMessage, testRecipients),
        "utf-8",
      );

      const startTime = Date.now();
      const decryptedMessage = await crypto.decryptMessage(encryptedContent);
      const endTime = Date.now();

      expect(decryptedMessage).toBe(largeMessage);
      expect(endTime - startTime).toBeLessThan(10000); // Should complete within 10 seconds
    });

    it("should handle concurrent decryption requests", async () => {
      const messages = [
        "First concurrent message",
        "Second concurrent message",
        "Third concurrent message",
      ];

      const encryptedMessages = await Promise.all(
        messages.map(async (msg) =>
          Buffer.from(await encryptMessage(msg, testRecipients), "utf-8"),
        ),
      );

      // Decrypt all messages concurrently
      const results = await Promise.all(
        encryptedMessages.map((encrypted) => crypto.decryptMessage(encrypted)),
      );

      expect(results).toEqual(messages);
    });

    it("removes temp dirs after sequential and concurrent file decryptions", async () => {
      const { filePath, cleanup } = createTestEncryptedFile(
        "cleanup stress content",
        "cleanup-stress.txt",
        testKeyId,
        gpgEnv.homedir,
      );
      const destinations = Array.from({ length: 4 }, () =>
        storage.createTempDir("securedrop-cleanup-target-"),
      );
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      const createTempDirSpy = vi
        .spyOn(storage, "createTempDir")
        .mockImplementation((prefix) => {
          const directory = createTempDir(prefix);
          operationDirectories.push(directory.path);
          return directory;
        });

      try {
        const results = [
          await crypto.decryptFile(storage, destinations[0], filePath),
          await crypto.decryptFile(storage, destinations[1], filePath),
          ...(await Promise.all(
            destinations
              .slice(2)
              .map((destination) =>
                crypto.decryptFile(storage, destination, filePath),
              ),
          )),
        ];

        expect(
          results.map((result) => fs.readFileSync(result, "utf8")),
        ).toEqual(Array(4).fill("cleanup stress content"));
        expect(operationDirectories).toHaveLength(4);
        expect(
          operationDirectories.every((directory) => !fs.existsSync(directory)),
        ).toBe(true);
      } finally {
        createTempDirSpy.mockRestore();
        cleanup();
        for (const destination of destinations) {
          fs.rmSync(destination.path, { force: true, recursive: true });
        }
      }
    });
  });

  describe("encryptMessage", () => {
    const plaintext = "Hello, SecureDrop!";
    const recipientPublicKeys = [
      "-----BEGIN PGP PUBLIC KEY BLOCK-----\n...\n-----END PGP PUBLIC KEY BLOCK-----",
      "-----BEGIN PGP PUBLIC KEY BLOCK-----\n...\n-----END PGP PUBLIC KEY BLOCK-----",
    ];

    const mockReadKey = vi.fn().mockResolvedValue("mockKey");
    const mockCreateMessage = vi.fn().mockResolvedValue("mockMessage");
    const mockEncrypt = vi.fn().mockResolvedValue("mockEncryptedText");

    beforeEach(() => {
      vi.mock("openpgp", { spy: true });
      vi.mocked(openpgp.readKey).mockImplementation(mockReadKey);
      vi.mocked(openpgp.createMessage).mockImplementation(mockCreateMessage);
      vi.mocked(openpgp.encrypt).mockImplementation(mockEncrypt);
    });

    afterEach(() => {
      vi.resetAllMocks();
    });

    it("successfully encrypts message to multiple recipients", async () => {
      const result = await encryptMessage(plaintext, recipientPublicKeys);
      expect(mockReadKey).toHaveBeenCalledTimes(recipientPublicKeys.length);
      for (const key of recipientPublicKeys) {
        expect(mockReadKey).toHaveBeenCalledWith({ armoredKey: key });
      }

      expect(mockCreateMessage).toHaveBeenCalledWith({ text: plaintext });

      expect(mockEncrypt).toHaveBeenCalledWith({
        message: "mockMessage",
        encryptionKeys: ["mockKey", "mockKey"],
      });

      expect(result).toBe("mockEncryptedText");
    });

    it("throws if openpgp.readKey fails", async () => {
      mockReadKey.mockRejectedValueOnce(new Error("bad key"));
      await expect(
        encryptMessage(plaintext, recipientPublicKeys),
      ).rejects.toThrow("bad key");
    });

    it("throws if openpgp.encrypt fails", async () => {
      mockEncrypt.mockRejectedValueOnce(new Error("encrypt error"));
      await expect(
        encryptMessage(plaintext, recipientPublicKeys),
      ).rejects.toThrow("encrypt error");
    });
  });

  describe("exportSubmissionKey", () => {
    it("should successfully export the submission key", async () => {
      // Reset and reinitialize with test key
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        isQubes: false,
        gpgHomedir: gpgEnv.homedir,
        submissionKeyFingerprint: testKeyId,
      });

      const exportedKey = await crypto.exportSubmissionKey();

      // Verify it's a valid PGP public key block
      expect(exportedKey).toContain("-----BEGIN PGP PUBLIC KEY BLOCK-----");
      expect(exportedKey).toContain("-----END PGP PUBLIC KEY BLOCK-----");

      // Verify we can read the key with openpgp
      const key = await openpgp.readKey({ armoredKey: exportedKey });
      expect(key).toBeTruthy();
    });

    it("should fail when exporting non-existent key", async () => {
      // Reset and reinitialize with non-existent fingerprint
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        isQubes: false,
        gpgHomedir: gpgEnv.homedir,
        submissionKeyFingerprint: "0000000000000000",
      });

      await expect(crypto.exportSubmissionKey()).rejects.toThrow();
    });
  });

  describe("getSubmissionKey", () => {
    it("should cache the submission key after first export", async () => {
      // Reset and reinitialize
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        isQubes: false,
        gpgHomedir: gpgEnv.homedir,
        submissionKeyFingerprint: testKeyId,
      });

      // First call should trigger export
      const key1 = await crypto.getSubmissionKey();
      expect(key1).toContain("-----BEGIN PGP PUBLIC KEY BLOCK-----");

      // Second call should return cached value (same string instance)
      const key2 = await crypto.getSubmissionKey();
      expect(key2).toBe(key1);

      // Verify the key is valid
      const key = await openpgp.readKey({ armoredKey: key1 });
      expect(key).toBeTruthy();
    });
  });

  describe("Message Decryption with source public key in keyring", () => {
    // Tests the scenario where the journalist has imported the source's public key,
    // so GPG emits two "encrypted with ... created ..." known-key blocks in stderr.
    let sourcePublicKey: string;
    let journalistPublicKey: string;

    beforeAll(() => {
      const testFilesDir = path.join(__dirname, "files");
      sourcePublicKey = fs.readFileSync(
        path.join(testFilesDir, "test-key.gpg.pub.asc"),
        "utf8",
      );

      // Import source public key into journalist keyring so GPG recognises both recipients
      gpgEnv.importKey(sourcePublicKey);

      // Export journalist public key for use in encryptMessage
      journalistPublicKey = execSync(
        `gpg --homedir "${gpgEnv.homedir}" --armor --export ${testKeyId}`,
        { encoding: "utf8" },
      );
    });

    it("should decrypt a message encrypted to both journalist and source keys", async () => {
      const originalMessage =
        "Secret message with source public key in journalist keyring";

      // Encrypt to both keys; since both are known to GPG, stderr will contain
      // two known-key blocks ("encrypted with ... created ... / UID")
      const encryptedContent = Buffer.from(
        await encryptMessage(originalMessage, [
          journalistPublicKey,
          sourcePublicKey,
        ]),
        "utf-8",
      );

      const decryptedMessage = await crypto.decryptMessage(encryptedContent);
      expect(decryptedMessage).toBe(originalMessage);
    });
  });

  describe("GPG stream failure modes (mocked spawn)", () => {
    afterEach(() => {
      vi.restoreAllMocks();
    });

    function makeMockProcess() {
      const proc = new EventEmitter() as any;
      proc.stdout = new PassThrough();
      proc.stderr = new PassThrough();
      proc.stdin = new PassThrough();
      proc.kill = vi.fn();
      return proc;
    }

    async function emitErrorOnNextTurn(
      stream: PassThrough,
      error: Error,
    ): Promise<void> {
      await new Promise<void>((resolve, reject) => {
        setImmediate(() => {
          try {
            stream.emit("error", error);
            resolve();
          } catch (emissionError) {
            reject(emissionError);
          }
        });
      });
    }

    function trackOperationDirectories(): string[] {
      const directories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        directories.push(directory.path);
        return directory;
      });
      return directories;
    }

    function expectOperationDirectoriesRemoved(directories: string[]): void {
      expect(directories).toHaveLength(1);
      expect(directories.every((entry) => !fs.existsSync(entry))).toBe(true);
    }

    it.each([
      ["stdout", "Failed to read GPG message output"],
      ["stderr", "Failed to read GPG diagnostics"],
    ])("handles a %s stream error before close", async (stream, message) => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptMessage(Buffer.from("encrypted"));
      const streamError = new Error(`${stream} read failed`);
      proc[stream].emit("error", streamError);
      proc.emit("close", 1, null);

      await expect(decryption).rejects.toThrow(message);
      expect(proc.kill).toHaveBeenCalledOnce();
      expect(() => proc[stream].emit("error", streamError)).not.toThrow();
    });

    it("absorbs stdout and stderr errors after successful close", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptMessage(Buffer.from("encrypted"));
      proc.stdout.end(Buffer.from("plaintext"));
      proc.emit("close", 0, null);

      await expect(decryption).resolves.toBe("plaintext");
      expect(() =>
        proc.stdout.emit("error", new Error("late stdout")),
      ).not.toThrow();
      expect(() =>
        proc.stderr.emit("error", new Error("late stderr")),
      ).not.toThrow();
    });

    it("allows an exact GPG lockfile diagnostic before expected key stderr", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptMessage(Buffer.from("encrypted"));
      proc.stdout.end(Buffer.from("plaintext"));
      proc.stderr.emit(
        "data",
        Buffer.from(
          "gpg: lockfile disappeared\n" +
            "gpg: encrypted with rsa4096 key, ID C3E7C4C0A2201B2A, created 2013-10-12\n" +
            '      "SecureDrop Test/Development (DO NOT USE IN PRODUCTION)"\n',
        ),
      );
      proc.emit("close", 0, null);

      await expect(decryption).resolves.toBe("plaintext");
    });

    it("settles once when stream errors race abort and process exit", async () => {
      const proc = makeMockProcess();
      const controller = new AbortController();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptMessage(
        Buffer.from("encrypted"),
        controller.signal,
      );
      controller.abort();

      expect(() =>
        proc.stdout.emit("error", new Error("stdout read failed")),
      ).not.toThrow();
      expect(() =>
        proc.stderr.emit("error", new Error("stderr read failed")),
      ).not.toThrow();
      expect(() =>
        proc.emit("error", new Error("process failed")),
      ).not.toThrow();
      proc.emit("close", null, "SIGTERM");

      await expect(decryption).rejects.toMatchObject({ name: "AbortError" });
      expect(proc.kill).toHaveBeenCalledOnce();
    });

    it("stops collecting a message after the decrypted byte limit", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptMessage(Buffer.from("encrypted"));
      const chunk = Buffer.alloc(1024 * 1024);
      for (
        let index = 0;
        index <= MAX_DECRYPTED_BYTES / chunk.length;
        index += 1
      ) {
        proc.stdout.emit("data", chunk);
      }
      proc.emit("close", null, "SIGTERM");

      await expect(promise).rejects.toThrow(
        `Decrypted message exceeds the ${MAX_DECRYPTED_BYTES}-byte limit`,
      );
      expect(proc.kill).toHaveBeenCalledOnce();
      const epipe = Object.assign(new Error("write EPIPE"), { code: "EPIPE" });
      expect(() => proc.stdin.emit("error", epipe)).not.toThrow();
    });

    it("rejects invalid UTF-8 instead of expanding replacement characters", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptMessage(Buffer.from("encrypted"));
      proc.stdout.emit("data", Buffer.from([0xff, 0xff, 0xff]));

      await expect(promise).rejects.toThrow(
        "Decrypted message is not valid UTF-8",
      );
      expect(proc.kill).toHaveBeenCalledOnce();
    });

    it("bounds hostile GPG stderr for messages", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptMessage(Buffer.from("encrypted"));
      proc.stderr.emit("data", Buffer.alloc(MAX_GPG_STDERR_BYTES + 1, 0x41));

      await expect(promise).rejects.toThrow(
        `GPG stderr exceeds the ${MAX_GPG_STDERR_BYTES}-byte limit`,
      );
      expect(proc.kill).toHaveBeenCalledOnce();
    });

    it("bounds hostile GPG stderr for files and removes operation state", async () => {
      const proc = makeMockProcess();
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        operationDirectories.push(directory.path);
        return directory;
      });
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
      );
      proc.stderr.emit("data", Buffer.alloc(MAX_GPG_STDERR_BYTES + 1, 0x41));

      await expect(promise).rejects.toThrow(
        `GPG stderr exceeds the ${MAX_GPG_STDERR_BYTES}-byte limit`,
      );
      expect(operationDirectories).toHaveLength(1);
      expect(fs.existsSync(operationDirectories[0])).toBe(false);
    });

    it("rejects a pre-aborted file signal without creating operation state", async () => {
      const controller = new AbortController();
      const createTempDir = vi.spyOn(storage, "createTempDir");
      controller.abort();

      await expect(
        crypto.decryptFile(
          storage,
          itemDirectory,
          "/fake/path.gpg",
          controller.signal,
        ),
      ).rejects.toMatchObject({ name: "AbortError" });
      expect(createTempDir).not.toHaveBeenCalled();
    });

    it("settles once when file output errors race cancellation", async () => {
      const proc = makeMockProcess();
      const controller = new AbortController();
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        operationDirectories.push(directory.path);
        return directory;
      });
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
        controller.signal,
      );
      controller.abort();
      expect(() =>
        proc.stdout.emit("error", new Error("late stdout")),
      ).not.toThrow();
      expect(() =>
        proc.stderr.emit("error", new Error("late stderr")),
      ).not.toThrow();
      proc.emit("close", null, "SIGTERM");

      await expect(decryption).rejects.toMatchObject({ name: "AbortError" });
      expect(proc.kill).toHaveBeenCalledOnce();
      expect(operationDirectories).toHaveLength(1);
      expect(fs.existsSync(operationDirectories[0])).toBe(false);
    });

    it("handles a file stderr stream error and removes operation state", async () => {
      const proc = makeMockProcess();
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        operationDirectories.push(directory.path);
        return directory;
      });
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
      );
      proc.stderr.emit("error", new Error("stderr read failed"));
      proc.emit("close", 1, null);

      await expect(decryption).rejects.toThrow(
        "Failed to read GPG diagnostics",
      );
      expect(proc.kill).toHaveBeenCalledOnce();
      expect(operationDirectories).toHaveLength(1);
      expect(fs.existsSync(operationDirectories[0])).toBe(false);
      expect(() =>
        proc.stderr.emit("error", new Error("late stderr")),
      ).not.toThrow();
    });

    it("preserves a file stdout error when child exit races cleanup", async () => {
      const proc = makeMockProcess();
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        operationDirectories.push(directory.path);
        return directory;
      });
      proc.kill.mockImplementation(() => {
        queueMicrotask(() => proc.emit("close", null, "SIGTERM"));
      });
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto
        .decryptFile(storage, itemDirectory, "/fake/path.gpg")
        .catch((error: unknown) => error);
      proc.stdout.emit("error", new Error("stdout read failed"));

      const error = await decryption;
      expect(error).toMatchObject({
        message: "Failed to write decrypted GPG output",
        cause: { message: "stdout read failed" },
      });
      expect(proc.kill).toHaveBeenCalledOnce();
      expect(operationDirectories).toHaveLength(1);
      expect(fs.existsSync(operationDirectories[0])).toBe(false);
      expect(() =>
        proc.stdout.emit("error", new Error("late stdout")),
      ).not.toThrow();
    });

    it("handles file stdin failure before close and consumes later errors", async () => {
      const proc = makeMockProcess();
      const operationDirectories = trackOperationDirectories();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const rejection = vi.fn();
      const decryption = crypto
        .decryptFile(storage, itemDirectory, "/fake/path.gpg")
        .catch((error: unknown) => {
          rejection(error);
          return error;
        });
      proc.stdin.emit("error", new Error("file stdin failed"));
      proc.emit("close", null, "SIGTERM");

      await expect(decryption).resolves.toMatchObject({
        message: "GPG file input stream failed",
        cause: { message: "file stdin failed" },
      });
      await emitErrorOnNextTurn(
        proc.stdin,
        new Error("later file stdin failed"),
      );
      expect(rejection).toHaveBeenCalledOnce();
      expect(proc.kill).toHaveBeenCalledOnce();
      expectOperationDirectoriesRemoved(operationDirectories);
    });

    it("handles file stdin failure after successful process close", async () => {
      const proc = makeMockProcess();
      const operationDirectories = trackOperationDirectories();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
      );
      proc.emit("close", 0, null);
      proc.stdin.emit("error", new Error("file stdin failed after close"));

      await expect(decryption).rejects.toMatchObject({
        message: "GPG file input stream failed",
        cause: { message: "file stdin failed after close" },
      });
      expect(proc.kill).toHaveBeenCalledOnce();
      expectOperationDirectoriesRemoved(operationDirectories);
    });

    it("consumes file stdin failure after decryptFile succeeds", async () => {
      const proc = makeMockProcess();
      const plaintext = Buffer.from("successful file plaintext");
      const operationDirectories = trackOperationDirectories();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const decryption = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
      );
      proc.stdout.end(gzipSync(plaintext));
      proc.emit("close", 0, null);

      const outputPath = await decryption;
      expect(fs.readFileSync(outputPath)).toEqual(plaintext);
      await emitErrorOnNextTurn(
        proc.stdin,
        new Error("late file stdin failed"),
      );
      expect(proc.kill).not.toHaveBeenCalled();
      expectOperationDirectoriesRemoved(operationDirectories);
    });

    it("settles once when file stdin failure races abort and exit", async () => {
      const proc = makeMockProcess();
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const rejection = vi.fn();
      const decryption = crypto
        .decryptFile(
          storage,
          itemDirectory,
          "/fake/path.gpg",
          controller.signal,
        )
        .catch((error: unknown) => {
          rejection(error);
          return error;
        });
      controller.abort();
      proc.stdin.emit("error", new Error("concurrent file stdin failed"));
      proc.emit("error", new Error("concurrent process failed"));
      proc.emit("close", null, "SIGTERM");

      await expect(decryption).resolves.toMatchObject({ name: "AbortError" });
      await emitErrorOnNextTurn(
        proc.stdin,
        new Error("post-race file stdin failed"),
      );
      expect(rejection).toHaveBeenCalledOnce();
      expect(proc.kill).toHaveBeenCalledOnce();
      expectOperationDirectoriesRemoved(operationDirectories);
    });

    it("throws CryptoError when GPG exits 0 with unexpected stderr (decryptMessage)", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptMessage(Buffer.from("fake encrypted data"));

      proc.stderr.emit(
        "data",
        Buffer.from("gpg: WARNING: unexpected warning\n"),
      );
      proc.stdout.end();
      proc.emit("close", 0, null);

      await expect(promise).rejects.toBeInstanceOf(CryptoError);
      await expect(promise).rejects.toThrow(/GPG decryption emitted stderr/);
    });

    it("throws CryptoError when GPG exits 0 with unexpected stderr (decryptFile)", async () => {
      const proc = makeMockProcess();
      vi.mocked(spawn).mockReturnValueOnce(proc);

      const promise = crypto.decryptFile(
        storage,
        itemDirectory,
        "/fake/path.gpg",
      );

      proc.stderr.emit(
        "data",
        Buffer.from("gpg: WARNING: unexpected warning\n"),
      );
      proc.stdout.end();
      proc.emit("close", 0, null);

      await expect(promise).rejects.toBeInstanceOf(CryptoError);
      await expect(promise).rejects.toThrow(
        /GPG file decryption emitted stderr/,
      );
    });
  });

  describe("file cancellation after GPG completion", () => {
    let largeFixture: EncryptedFileFixture;

    beforeAll(async () => {
      largeFixture = await createLargeEncryptedFile(
        MAX_DECRYPTED_BYTES,
        testKeyId,
        gpgEnv.homedir,
      );
    }, 60_000);

    afterAll(() => {
      largeFixture.cleanup();
    });

    afterEach(() => {
      vi.restoreAllMocks();
    });

    function trackOperationDirectories(): string[] {
      const directories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      vi.spyOn(storage, "createTempDir").mockImplementation((prefix) => {
        const directory = createTempDir(prefix);
        directories.push(directory.path);
        return directory;
      });
      return directories;
    }

    function expectNoDecryptResidue(operationDirectories: string[]): void {
      expect(operationDirectories).toHaveLength(1);
      expect(operationDirectories.every((entry) => !fs.existsSync(entry))).toBe(
        true,
      );
      expect(fs.readdirSync(itemDirectory.path)).toEqual([]);
    }

    async function expectBoundaryCancellation(
      configure: (controller: AbortController) => void,
    ): Promise<void> {
      const fixture = createTestEncryptedFile(
        Buffer.alloc(4 * 1024 * 1024, 0x42),
        "boundary-fixture.bin",
        testKeyId,
        gpgEnv.homedir,
      );
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      configure(controller);
      try {
        await expect(
          crypto.decryptFile(
            storage,
            itemDirectory,
            fixture.filePath,
            controller.signal,
          ),
        ).rejects.toMatchObject({ name: "AbortError" });
        expectNoDecryptResidue(operationDirectories);
      } finally {
        fixture.cleanup();
      }
    }

    async function expectBoundaryCompletion(
      configure: (controller: AbortController) => void,
    ): Promise<void> {
      const plaintext = Buffer.from("published plaintext");
      const fixture = createTestEncryptedFile(
        plaintext,
        "published-fixture.bin",
        testKeyId,
        gpgEnv.homedir,
      );
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      configure(controller);
      try {
        const outputPath = await crypto.decryptFile(
          storage,
          itemDirectory,
          fixture.filePath,
          controller.signal,
        );
        expect(controller.signal.aborted).toBe(true);
        expect(outputPath).toBe(itemDirectory.join("published-fixture.bin"));
        expect(fs.readFileSync(outputPath)).toEqual(plaintext);
        expect(operationDirectories).toHaveLength(1);
        expect(
          operationDirectories.every((entry) => !fs.existsSync(entry)),
        ).toBe(true);
      } finally {
        fixture.cleanup();
      }
    }

    it.each([
      ["first", 1],
      ["middle", MAX_DECRYPTED_BYTES / 2],
      ["last", MAX_DECRYPTED_BYTES],
    ])(
      "cancels a 500 MiB real-GPG file on the %s gunzip plaintext chunk",
      async (_position, targetBytes) => {
        const controller = new AbortController();
        const operationDirectories = trackOperationDirectories();
        const writes = abortPlaintextAtSize(controller, targetBytes);

        try {
          await expect(
            crypto.decryptFile(
              storage,
              itemDirectory,
              largeFixture.filePath,
              controller.signal,
            ),
          ).rejects.toMatchObject({ name: "AbortError" });
        } finally {
          writes.stop();
        }

        expect(controller.signal.aborted).toBe(true);
        expect(writes.maxBytes()).toBeGreaterThanOrEqual(targetBytes);
        expect(writes.maxBytes()).toBeLessThan(targetBytes + 64 * 1024 * 1024);
        expectNoDecryptResidue(operationDirectories);
      },
      180_000,
    );

    it("cancels gzip header validation", async () => {
      await expectBoundaryCancellation((controller) => {
        const open = fs.promises.open.bind(fs.promises);
        vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
          const file = await open(...args);
          if (path.basename(String(args[0])) === "decrypted.gz") {
            const read = file.read.bind(file);
            vi.spyOn(file, "read").mockImplementation(async (...readArgs) => {
              const result = await read(...readArgs);
              controller.abort();
              return result;
            });
          }
          return file;
        });
      });
    });

    it("prefers header cancellation to a concurrent read error", async () => {
      await expectBoundaryCancellation((controller) => {
        const open = fs.promises.open.bind(fs.promises);
        vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
          const file = await open(...args);
          if (path.basename(String(args[0])) === "decrypted.gz") {
            vi.spyOn(file, "read").mockImplementation(async () => {
              controller.abort();
              throw new Error("header read failed");
            });
          }
          return file;
        });
      });
    });

    it.each(["before", "after"] as const)(
      "cancels %s final-file fsync completion",
      async (timing) => {
        await expectBoundaryCancellation((controller) => {
          const open = fs.promises.open.bind(fs.promises);
          vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
            const file = await open(...args);
            if (path.basename(String(args[0])) !== "plaintext") {
              return file;
            }
            const sync = file.sync.bind(file);
            vi.spyOn(file, "sync").mockImplementation(async () => {
              if (timing === "before") {
                controller.abort();
              }
              await sync();
              if (timing === "after") {
                controller.abort();
              }
            });
            return file;
          });
        });
      },
    );

    it("prefers fsync cancellation to a concurrent sync error", async () => {
      await expectBoundaryCancellation((controller) => {
        const open = fs.promises.open.bind(fs.promises);
        vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
          const file = await open(...args);
          if (path.basename(String(args[0])) === "plaintext") {
            vi.spyOn(file, "sync").mockImplementation(async () => {
              controller.abort();
              throw new Error("fsync failed");
            });
          }
          return file;
        });
      });
    });

    it("does not publish when cancellation happens before final link", async () => {
      let linkCalls = 0;
      await expectBoundaryCancellation((controller) => {
        const open = fs.promises.open.bind(fs.promises);
        vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
          const file = await open(...args);
          if (path.basename(String(args[0])) === "plaintext") {
            const sync = file.sync.bind(file);
            vi.spyOn(file, "sync").mockImplementation(async () => {
              await sync();
              controller.abort();
            });
          }
          return file;
        });
        const link = fs.promises.link.bind(fs.promises);
        vi.spyOn(fs.promises, "link").mockImplementation(async (...args) => {
          linkCalls += 1;
          await link(...args);
        });
      });
      expect(linkCalls).toBe(0);
    });

    it("keeps the committed file when cancellation happens after final link", async () => {
      await expectBoundaryCompletion((controller) => {
        const link = fs.promises.link.bind(fs.promises);
        vi.spyOn(fs.promises, "link").mockImplementation(async (...args) => {
          await link(...args);
          controller.abort();
        });
      });
    });

    it("prefers publication cancellation to a concurrent link error", async () => {
      await expectBoundaryCancellation((controller) => {
        vi.spyOn(fs.promises, "link").mockImplementation(async () => {
          controller.abort();
          throw new Error("link failed");
        });
      });
    });

    it("falls back to rmSync when async temp cleanup fails", async () => {
      await expectBoundaryCancellation((controller) => {
        const open = fs.promises.open.bind(fs.promises);
        vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
          const file = await open(...args);
          if (path.basename(String(args[0])) === "plaintext") {
            const sync = file.sync.bind(file);
            vi.spyOn(file, "sync").mockImplementation(async () => {
              controller.abort();
              await sync();
            });
          }
          return file;
        });

        const rm = fs.promises.rm.bind(fs.promises);
        vi.spyOn(fs.promises, "rm").mockImplementation(async (...args) => {
          if (
            path.basename(String(args[0])).startsWith(".securedrop-decrypt-")
          ) {
            throw new Error("temp async rm failed");
          }
          return rm(...args);
        });
      });
    });

    it("does not replace an existing final file after cancellation", async () => {
      const fixture = createTestEncryptedFile(
        Buffer.from("replacement"),
        "boundary-fixture.bin",
        testKeyId,
        gpgEnv.homedir,
      );
      const finalOutputPath = itemDirectory.join("boundary-fixture.bin");
      const originalContent = Buffer.from("original");
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      const link = fs.promises.link.bind(fs.promises);
      vi.spyOn(fs.promises, "link").mockImplementation(async (...args) => {
        controller.abort();
        await link(...args);
      });
      fs.writeFileSync(finalOutputPath, originalContent);

      try {
        await expect(
          crypto.decryptFile(
            storage,
            itemDirectory,
            fixture.filePath,
            controller.signal,
          ),
        ).rejects.toMatchObject({ name: "AbortError" });
        expect(operationDirectories).toHaveLength(1);
        expect(
          operationDirectories.every((entry) => !fs.existsSync(entry)),
        ).toBe(true);
        expect(fs.readFileSync(finalOutputPath)).toEqual(originalContent);
      } finally {
        fixture.cleanup();
      }
    });

    it("keeps the committed file when cancellation crosses helper completion", async () => {
      await expectBoundaryCompletion((controller) => {
        const link = fs.promises.link.bind(fs.promises);
        vi.spyOn(fs.promises, "link").mockImplementation(async (...args) => {
          await link(...args);
          let checkpoints = 4;
          const abortAfterCheckpoints = () => {
            if (checkpoints === 0) {
              controller.abort();
              return;
            }
            checkpoints -= 1;
            queueMicrotask(abortAfterCheckpoints);
          };
          queueMicrotask(abortAfterCheckpoints);
        });
      });
    });

    it("propagates cancellation through a qubes-gpg-client shim", async () => {
      const fixture = createTestEncryptedFile(
        Buffer.alloc(4 * 1024 * 1024, 0x43),
        "qubes-shim-fixture.bin",
        testKeyId,
        gpgEnv.homedir,
      );
      const shimDirectory = fs.mkdtempSync(
        path.join(os.tmpdir(), "qubes-gpg-client-test-"),
      );
      const shimPath = path.join(shimDirectory, "qubes-gpg-client");
      fs.writeFileSync(
        shimPath,
        '#!/bin/sh\nexec gpg --homedir "$SD_TEST_GPG_HOME" "$@"\n',
        { mode: 0o755 },
      );
      const originalPath = process.env.PATH;
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      const open = fs.promises.open.bind(fs.promises);
      vi.spyOn(fs.promises, "open").mockImplementation(async (...args) => {
        const file = await open(...args);
        if (path.basename(String(args[0])) === "plaintext") {
          const sync = file.sync.bind(file);
          vi.spyOn(file, "sync").mockImplementation(async () => {
            controller.abort();
            await sync();
          });
        }
        return file;
      });

      try {
        process.env.PATH = `${shimDirectory}:${originalPath}`;
        process.env.SD_TEST_GPG_HOME = gpgEnv.homedir;
        (Crypto as any).instance = undefined;
        const qubesCrypto = Crypto.initialize({
          isQubes: true,
          submissionKeyFingerprint: "",
        });
        await expect(
          qubesCrypto.decryptFile(
            storage,
            itemDirectory,
            fixture.filePath,
            controller.signal,
          ),
        ).rejects.toMatchObject({ name: "AbortError" });
        expectNoDecryptResidue(operationDirectories);
      } finally {
        process.env.PATH = originalPath;
        delete process.env.SD_TEST_GPG_HOME;
        fixture.cleanup();
        fs.rmSync(shimDirectory, { force: true, recursive: true });
      }
    });

    it("prefers an observed gunzip cancellation over a later stream error", async () => {
      const fixtureDirectory = fs.mkdtempSync(
        path.join(os.tmpdir(), "crypto-cancel-error-race-"),
      );
      const malformedPath = path.join(fixtureDirectory, "malformed.gz");
      const encryptedPath = `${malformedPath}.gpg`;
      const gzipPayload = gzipSync(Buffer.alloc(64 * 1024 * 1024, 0x44));
      fs.writeFileSync(
        malformedPath,
        gzipPayload.subarray(0, gzipPayload.length - 8),
      );
      execFileSync("gpg", [
        "--homedir",
        gpgEnv.homedir,
        "--batch",
        "--trust-model",
        "always",
        "--encrypt",
        "-r",
        testKeyId,
        "--output",
        encryptedPath,
        malformedPath,
      ]);
      const controller = new AbortController();
      const operationDirectories = trackOperationDirectories();
      const writes = abortPlaintextAtSize(controller, 1);

      try {
        await expect(
          crypto.decryptFile(
            storage,
            itemDirectory,
            encryptedPath,
            controller.signal,
          ),
        ).rejects.toMatchObject({ name: "AbortError" });
        expectNoDecryptResidue(operationDirectories);
      } finally {
        writes.stop();
        fs.rmSync(fixtureDirectory, { force: true, recursive: true });
      }
    });
  });

  describe("decrypted byte limit", () => {
    async function streamBytes(chunks: Buffer[], maxBytes: number) {
      const output: Buffer[] = [];
      await pipeline(
        Readable.from(chunks),
        createDecryptedByteLimit("Test output", maxBytes),
        new Writable({
          write(chunk: Buffer, _encoding, callback) {
            output.push(chunk);
            callback();
          },
        }),
      );
      return Buffer.concat(output);
    }

    async function discardBytes(byteCount: number, maxBytes: number) {
      const chunk = Buffer.alloc(64 * 1024 * 1024);
      function* chunks() {
        let remaining = byteCount;
        while (remaining > 0) {
          const bytes = Math.min(remaining, chunk.length);
          yield chunk.subarray(0, bytes);
          remaining -= bytes;
        }
      }
      await pipeline(
        Readable.from(chunks()),
        createDecryptedByteLimit("Test output", maxBytes),
        new Writable({
          write(_chunk, _encoding, callback) {
            callback();
          },
        }),
      );
    }

    it("rejects a real OpenPGP packet one byte over the intermediate limit", async () => {
      const fixture = await createStoredOpenPgpFile(
        MAX_DECRYPTED_GZIP_BYTES + 1,
        gpgEnv.homedir,
      );
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      const createTempDirSpy = vi
        .spyOn(storage, "createTempDir")
        .mockImplementation((prefix) => {
          const directory = createTempDir(prefix);
          operationDirectories.push(directory.path);
          return directory;
        });

      try {
        await expect(
          crypto.decryptFile(storage, itemDirectory, fixture.filePath),
        ).rejects.toMatchObject({
          message: "Failed to write decrypted GPG output",
          cause: {
            message: `GPG-decrypted file exceeds the ${MAX_DECRYPTED_GZIP_BYTES}-byte limit`,
          },
        });
        expect(operationDirectories).toHaveLength(1);
        expect(
          operationDirectories.every((entry) => !fs.existsSync(entry)),
        ).toBe(true);
        expect(fs.readdirSync(itemDirectory.path)).toEqual([]);
      } finally {
        createTempDirSpy.mockRestore();
        fixture.cleanup();
      }
    }, 180_000);

    it("rejects a real-GPG gzip member one byte over the production limit", async () => {
      const fixture = await createLargeEncryptedFile(
        MAX_DECRYPTED_BYTES + 1,
        testKeyId,
        gpgEnv.homedir,
      );
      const operationDirectories: string[] = [];
      const createTempDir = storage.createTempDir.bind(storage);
      const createTempDirSpy = vi
        .spyOn(storage, "createTempDir")
        .mockImplementation((prefix) => {
          const directory = createTempDir(prefix);
          operationDirectories.push(directory.path);
          return directory;
        });

      try {
        await expect(
          crypto.decryptFile(storage, itemDirectory, fixture.filePath),
        ).rejects.toMatchObject({
          message: "Failed to decompress decrypted file",
          cause: {
            message: `Decompressed file exceeds the ${MAX_DECRYPTED_BYTES}-byte limit`,
          },
        });
        expect(operationDirectories).toHaveLength(1);
        expect(
          operationDirectories.every((entry) => !fs.existsSync(entry)),
        ).toBe(true);
        expect(fs.readdirSync(itemDirectory.path)).toEqual([]);
      } finally {
        createTempDirSpy.mockRestore();
        fixture.cleanup();
      }
    }, 180_000);

    it("allows output exactly at the limit", async () => {
      const output = await streamBytes([Buffer.alloc(4), Buffer.alloc(4)], 8);
      expect(output).toHaveLength(8);
    });

    it("rejects the first byte over the limit", async () => {
      await expect(
        streamBytes([Buffer.alloc(8), Buffer.alloc(1)], 8),
      ).rejects.toThrow("Test output exceeds the 8-byte limit");
    });

    it("allows plaintext exactly at the production limit", async () => {
      await expect(
        discardBytes(MAX_DECRYPTED_BYTES, MAX_DECRYPTED_BYTES),
      ).resolves.toBeUndefined();
    });

    it("rejects plaintext one byte over the production limit", async () => {
      await expect(
        discardBytes(MAX_DECRYPTED_BYTES + 1, MAX_DECRYPTED_BYTES),
      ).rejects.toThrow(
        `Test output exceeds the ${MAX_DECRYPTED_BYTES}-byte limit`,
      );
    });

    it("allows intermediate gzip exactly at its production limit", async () => {
      await expect(
        discardBytes(MAX_DECRYPTED_GZIP_BYTES, MAX_DECRYPTED_GZIP_BYTES),
      ).resolves.toBeUndefined();
    });

    it("rejects intermediate gzip one byte over its production limit", async () => {
      await expect(
        discardBytes(MAX_DECRYPTED_GZIP_BYTES + 1, MAX_DECRYPTED_GZIP_BYTES),
      ).rejects.toThrow(
        `Test output exceeds the ${MAX_DECRYPTED_GZIP_BYTES}-byte limit`,
      );
    });

    it("derives the gzip allowance from compression and framing", () => {
      const compressBound =
        MAX_DECRYPTED_BYTES +
        Math.floor(MAX_DECRYPTED_BYTES / 4096) +
        Math.floor(MAX_DECRYPTED_BYTES / 16384) +
        Math.floor(MAX_DECRYPTED_BYTES / 33554432) +
        13;
      expect(MAX_DECRYPTED_GZIP_BYTES).toBe(compressBound + 1024 + 8);
    });
  });

  describe("encryptSourceMessage", () => {
    it("should encrypt message to both source and journalist keys", async () => {
      // Reset and reinitialize
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        isQubes: false,
        gpgHomedir: gpgEnv.homedir,
        submissionKeyFingerprint: testKeyId,
      });

      const plaintext = "Secret message to source";

      // Export the test key as "source public key"
      const sourcePublicKey = await crypto.exportSubmissionKey();

      // Encrypt the message
      const encrypted = await crypto.encryptSourceMessage(
        plaintext,
        sourcePublicKey,
      );

      // Verify it's encrypted
      expect(encrypted).toContain("-----BEGIN PGP MESSAGE-----");
      expect(encrypted).toContain("-----END PGP MESSAGE-----");

      // Decrypt with GPG to verify it matches the original plaintext
      const decrypted = await crypto.decryptMessage(Buffer.from(encrypted));
      expect(decrypted).toBe(plaintext);
    });
  });
});
