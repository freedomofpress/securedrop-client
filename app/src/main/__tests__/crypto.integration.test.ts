import { describe, it, expect, beforeEach, vi, afterEach } from "vitest";
import { spawn } from "child_process";
import * as fs from "fs";
import { Crypto, CryptoError } from "../crypto";
import { Storage, PathBuilder, UnsafePathComponent } from "../storage";

// Mock fs for testing
vi.mock("fs");
vi.mock("child_process");
vi.mock("os", () => ({
  default: {
    homedir: vi.fn(() => "/tmp/test-home"),
    tmpdir: vi.fn(() => "/tmp"),
  },
}));

const mockFs = vi.mocked(fs);
const mockSpawn = vi.mocked(spawn);

// Type definition for testing private methods
type CryptoWithPrivateMethods = {
  getGpgCommand(): string[];
  readGzipHeaderFilename(data: Buffer): UnsafePathComponent | null;
  decompressGzip(data: Buffer): Promise<string>;
  readGzipHeaderFilenameFromFile(filePath: string): Promise<string>;
  streamDecompressGzipFile(
    gzipFilePath: string,
    outputPath: string,
  ): Promise<void>;
};

describe("Crypto Integration Tests", () => {
  let mockProcess: {
    stdin: { write: ReturnType<typeof vi.fn>; end: ReturnType<typeof vi.fn> };
    stdout: { on: ReturnType<typeof vi.fn>; pipe: ReturnType<typeof vi.fn> };
    stderr: { on: ReturnType<typeof vi.fn> };
    on: ReturnType<typeof vi.fn>;
  };
  let storage: Storage;
  let itemDirectory: PathBuilder;

  beforeEach(() => {
    // Reset singleton instance for testing
    (Crypto as any).instance = undefined;
    vi.clearAllMocks();
    vi.unstubAllEnvs();

    // Mock fs functions needed by Storage
    (mockFs.realpathSync as any) = vi.fn((path) => path);
    (mockFs.existsSync as any) = vi.fn(() => false);
    (mockFs.mkdirSync as any) = vi.fn();

    // Mock process object for spawn
    mockProcess = {
      stdin: {
        write: vi.fn(),
        end: vi.fn(),
      },
      stdout: {
        on: vi.fn(),
        pipe: vi.fn(),
      },
      stderr: {
        on: vi.fn(),
      },
      on: vi.fn(),
    };

    // Create real Storage and PathBuilder instances
    storage = new Storage();
    itemDirectory = new PathBuilder("/tmp/test-item/");
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  describe("Message Decryption", () => {
    it("should successfully decrypt a message (non-doc)", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });
      const testMessage = "Test message content";
      const encryptedContent = Buffer.from("encrypted-content");

      // Mock GPG process for successful decryption
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            // Simulate successful GPG exit
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stdout.on.mockImplementation(
        (event: string, callback: (data: Buffer) => void) => {
          if (event === "data") {
            // Simulate GPG output (decrypted content - no gzip decompression for messages)
            setTimeout(() => callback(Buffer.from(testMessage)), 5);
          }
          return mockProcess;
        },
      );

      mockProcess.stderr.on.mockImplementation(
        (_event: string, _callback: (data: Buffer) => void) => {
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      const result = await crypto.decryptMessage(encryptedContent);

      expect(result).toBe(testMessage);
      expect(mockSpawn).toHaveBeenCalledWith("gpg", [
        "--trust-model",
        "always",
        "--decrypt",
      ]);
      expect(mockProcess.stdin.write).toHaveBeenCalledWith(encryptedContent);
      expect(mockProcess.stdin.end).toHaveBeenCalled();
    });

    it("should handle GPG decryption failure for messages", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const encryptedContent = Buffer.from("bad-encrypted-content");

      // Mock GPG process for failed decryption
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            // Simulate GPG failure
            setTimeout(() => callback(1), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stderr.on.mockImplementation(
        (event: string, callback: (data: Buffer) => void) => {
          if (event === "data") {
            setTimeout(() => callback(Buffer.from("GPG decryption error")), 5);
          }
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await expect(crypto.decryptMessage(encryptedContent)).rejects.toThrow(
        CryptoError,
      );
      await expect(crypto.decryptMessage(encryptedContent)).rejects.toThrow(
        "GPG decryption failed (exit code 1): GPG decryption error",
      );
    });

    it("should handle GPG process spawn failure", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const encryptedContent = Buffer.from("encrypted-content");

      // Mock spawn failure
      mockProcess.on.mockImplementation(
        (event: string, callback: (error: Error) => void) => {
          if (event === "error") {
            setTimeout(() => callback(new Error("Process spawn failed")), 5);
          }
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await expect(crypto.decryptMessage(encryptedContent)).rejects.toThrow(
        CryptoError,
      );
      await expect(crypto.decryptMessage(encryptedContent)).rejects.toThrow(
        "Failed to start GPG process: Process spawn failed",
      );
    });
  });

  describe("File Decryption", () => {
    beforeEach(() => {
      // Mock filesystem operations
      mockFs.createWriteStream.mockReturnValue({
        end: vi.fn(),
      } as never);

      mockFs.createReadStream.mockReturnValue({
        pipe: vi.fn(),
      } as never);

      mockFs.unlink.mockImplementation((_path, callback) => {
        if (callback) callback(null);
      });

      mockFs.existsSync.mockReturnValue(true);
      mockFs.mkdtempSync.mockReturnValue("/tmp/test-temp");
      mockFs.realpathSync.mockImplementation((path) => path as string);
      mockFs.rmSync.mockImplementation(() => {});
    });

    it("should successfully decrypt and decompress a gzipped file", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const testFilePath = "/path/to/encrypted-file.gpg";

      // Mock successful GPG process
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stderr.on.mockImplementation(() => mockProcess);

      // Mock the private methods that would handle gzip
      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      vi.spyOn(
        cryptoWithPrivate,
        "readGzipHeaderFilenameFromFile",
      ).mockResolvedValue("original-file.txt");
      vi.spyOn(
        cryptoWithPrivate,
        "streamDecompressGzipFile",
      ).mockResolvedValue();

      mockSpawn.mockReturnValue(mockProcess as never);

      const result = await crypto.decryptFile(
        storage,
        itemDirectory,
        testFilePath,
      );

      expect(result).toMatch(/original-file\.txt$/);
      expect(mockSpawn).toHaveBeenCalledWith("gpg", [
        "--trust-model",
        "always",
        "--decrypt",
        testFilePath,
      ]);
    });

    it("should handle file decryption failure", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const testFilePath = "/path/to/encrypted-file.gpg";

      // Mock failed GPG process
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(2), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stderr.on.mockImplementation(
        (event: string, callback: (data: Buffer) => void) => {
          if (event === "data") {
            setTimeout(
              () => callback(Buffer.from("GPG file decryption error")),
              5,
            );
          }
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await expect(
        crypto.decryptFile(storage, itemDirectory, testFilePath),
      ).rejects.toThrow(CryptoError);
      await expect(
        crypto.decryptFile(storage, itemDirectory, testFilePath),
      ).rejects.toThrow(
        "GPG file decryption failed (exit code 2): GPG file decryption error",
      );
    });

    it("should use fallback filename when gzip header has no filename", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const testFilePath = "/path/to/encrypted-file.gpg";

      // Mock successful GPG process
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stderr.on.mockImplementation(() => mockProcess);

      // Mock no filename in gzip header
      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      vi.spyOn(
        cryptoWithPrivate,
        "readGzipHeaderFilenameFromFile",
      ).mockResolvedValue("");
      vi.spyOn(
        cryptoWithPrivate,
        "streamDecompressGzipFile",
      ).mockResolvedValue();

      mockSpawn.mockReturnValue(mockProcess as never);

      const result = await crypto.decryptFile(
        storage,
        itemDirectory,
        testFilePath,
      );

      expect(result).toMatch(/encrypted-file$/); // Falls back to basename without .gpg
      expect(mockSpawn).toHaveBeenCalled();
    });

    it("should handle decompression failure", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });

      const testFilePath = "/path/to/encrypted-file.gpg";

      // Mock successful GPG but failed decompression
      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      vi.spyOn(
        cryptoWithPrivate,
        "readGzipHeaderFilenameFromFile",
      ).mockResolvedValue("test.txt");
      vi.spyOn(cryptoWithPrivate, "streamDecompressGzipFile").mockRejectedValue(
        new Error("Decompression failed"),
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await expect(
        crypto.decryptFile(storage, itemDirectory, testFilePath),
      ).rejects.toThrow(CryptoError);
      await expect(
        crypto.decryptFile(storage, itemDirectory, testFilePath),
      ).rejects.toThrow("Failed to decompress decrypted file");
    });
  });

  describe("Environment-specific behavior", () => {
    it("should use qubes-gpg-client in Qubes environment", async () => {
      const crypto = Crypto.initialize({
        journalistPublicKey: "",
        isQubes: true,
      });

      const encryptedContent = Buffer.from("test");

      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stdout.on.mockImplementation(
        (event: string, callback: (data: Buffer) => void) => {
          if (event === "data") {
            setTimeout(() => callback(Buffer.from("decrypted")), 5);
          }
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await crypto.decryptMessage(encryptedContent);

      expect(mockSpawn).toHaveBeenCalledWith("qubes-gpg-client", [
        "--trust-model",
        "always",
        "--decrypt",
      ]);
    });

    it("should use custom homedir when specified", async () => {
      const crypto = Crypto.initialize({
        isQubes: false,
        gpgHomedir: "/custom/gnupg",
        journalistPublicKey: "",
      });

      const encryptedContent = Buffer.from("test");

      mockProcess.on.mockImplementation(
        (event: string, callback: (code: number) => void) => {
          if (event === "close") {
            setTimeout(() => callback(0), 10);
          }
          return mockProcess;
        },
      );

      mockProcess.stdout.on.mockImplementation(
        (event: string, callback: (data: Buffer) => void) => {
          if (event === "data") {
            setTimeout(() => callback(Buffer.from("decrypted")), 5);
          }
          return mockProcess;
        },
      );

      mockSpawn.mockReturnValue(mockProcess as never);

      await crypto.decryptMessage(encryptedContent);

      expect(mockSpawn).toHaveBeenCalledWith("gpg", [
        "--trust-model",
        "always",
        "--homedir",
        "/custom/gnupg",
        "--decrypt",
      ]);
    });
  });

  describe("Gzip Header Processing", () => {
    let crypto: Crypto;

    beforeEach(() => {
      crypto = Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });
    });

    it("should extract filename from gzip header with extra fields", () => {
      // Create gzip header with FEXTRA and FNAME flags
      const filename = "test-document.txt";
      const extraData = Buffer.from([0xaa, 0xbb]); // 2 bytes of extra data

      const header = Buffer.concat([
        Buffer.from([0x1f, 0x8b]), // gzip magic
        Buffer.from([0x08]), // compression method
        Buffer.from([0x08 | 0x04]), // flags: FNAME | FEXTRA
        Buffer.from([0x00, 0x00, 0x00, 0x00]), // mtime
        Buffer.from([0x00]), // extra flags
        Buffer.from([0x03]), // OS
        Buffer.from([extraData.length, 0x00]), // extra length (little endian)
        extraData, // extra data
        Buffer.from(filename), // filename
        Buffer.from([0x00]), // null terminator
      ]);

      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      const result = cryptoWithPrivate.readGzipHeaderFilename(header);
      expect(result?.path).toBe(filename);
    });

    it("should handle incomplete gzip header gracefully", () => {
      const incompleteHeader = Buffer.from([0x1f, 0x8b, 0x08]); // Too short

      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      expect(() => {
        cryptoWithPrivate.readGzipHeaderFilename(incompleteHeader);
      }).toThrow("Data too short to be a valid gzip file");
    });

    it("should handle filename not null-terminated", () => {
      const header = Buffer.from([
        0x1f,
        0x8b, // gzip magic
        0x08, // compression method
        0x08, // flags: FNAME
        0x00,
        0x00,
        0x00,
        0x00, // mtime
        0x00, // extra flags
        0x03, // OS
        // filename without null terminator
        0x74,
        0x65,
        0x73,
        0x74, // "test" but no null terminator
      ]);

      const cryptoWithPrivate = crypto as unknown as CryptoWithPrivateMethods;
      expect(() => {
        cryptoWithPrivate.readGzipHeaderFilename(header);
      }).toThrow("Filename in gzip header not null-terminated");
    });
  });

  describe("Singleton behavior", () => {
    it("should return the same instance on multiple calls", () => {
      Crypto.initialize({ journalistPublicKey: "", isQubes: false });
      const crypto1 = Crypto.getInstance();
      const crypto2 = Crypto.getInstance();
      expect(crypto1).toBe(crypto2);
    });

    it("should throw error when trying to initialize twice", () => {
      Crypto.initialize({
        isQubes: false,
        journalistPublicKey: "",
      });
      expect(() => {
        Crypto.initialize({ isQubes: true, journalistPublicKey: "" });
      }).toThrow(
        "Crypto already initialized: cannot initialize twice. Call initialize() before getInstance().",
      );
    });
  });
});
