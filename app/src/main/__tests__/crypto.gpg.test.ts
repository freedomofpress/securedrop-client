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
import { Crypto, CryptoError } from "../crypto";
import {
  createGpgTestEnvironment,
  createTestEncryptedContent,
  createTestEncryptedFile,
  verifyGpgAvailable,
  loadTestKeys,
  type GpgTestEnvironment,
} from "./setup-gpg-tests";
import { PathBuilder, Storage } from "../storage";

// Verify GPG is available - fail tests if not
const isGpgAvailable = verifyGpgAvailable();

describe("Crypto with Real GPG", () => {
  let gpgEnv: GpgTestEnvironment;
  let crypto: Crypto;
  let testKeyId: string;
  const storage = new Storage();
  let itemDirectory: PathBuilder;

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
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    (Crypto as any).instance = undefined;
    Crypto.initialize({
      isQubes: false,
      gpgHomedir: gpgEnv.homedir,
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
      const encryptedContent = createTestEncryptedContent(
        originalMessage,
        testKeyId,
        gpgEnv.homedir,
      );

      // Decrypt using our crypto class
      const decryptedMessage = await crypto.decryptMessage(encryptedContent);

      expect(decryptedMessage).toBe(originalMessage);
    });

    it("should decrypt a message with newlines and special characters", async () => {
      const originalMessage = `This is a multi-line message
with special characters: àáâãäåæçèéêë
and symbols: !@#$%^&*()_+-={}[]|\\:";'<>?,./`;

      const encryptedContent = createTestEncryptedContent(
        originalMessage,
        testKeyId,
        gpgEnv.homedir,
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

      const encryptedContent = createTestEncryptedContent(
        originalMessage,
        testKeyId,
        gpgEnv.homedir,
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
      } finally {
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
      const encryptedMessage = createTestEncryptedContent(
        testData,
        testKeyId,
        gpgEnv.homedir,
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

      const encryptedContent = createTestEncryptedContent(
        largeMessage,
        testKeyId,
        gpgEnv.homedir,
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

      const encryptedMessages = messages.map((msg) =>
        createTestEncryptedContent(msg, testKeyId, gpgEnv.homedir),
      );

      // Decrypt all messages concurrently
      const results = await Promise.all(
        encryptedMessages.map((encrypted) => crypto.decryptMessage(encrypted)),
      );

      expect(results).toEqual(messages);
    });
  });
});
