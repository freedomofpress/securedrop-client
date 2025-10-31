import { describe, it, expect, beforeEach, vi, afterEach } from "vitest";
import { Crypto, CryptoError } from "../crypto";
import { UnsafePathComponent } from "../storage";

// Type definition for testing private methods
type CryptoWithPrivateMethods = {
  getGpgCommand(): string[];
  readGzipHeaderFilename(data: Buffer): UnsafePathComponent | null;
};

describe("Crypto", () => {
  afterEach(() => {
    vi.clearAllMocks();
    vi.unstubAllEnvs();
  });

  describe("getInstance and Qubes detection", () => {
    beforeEach(() => {
      // Reset singleton instance for testing
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      (Crypto as any).instance = undefined;
    });

    it("should detect Qubes when QUBES_ environment variable exists", () => {
      vi.stubEnv("QUBES_SOMETHING", "value");
      Crypto.initialize({});
      const crypto = Crypto.getInstance();

      // Test by checking internal state via the getGpgCommand private method
      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("qubes-gpg-client");
      expect(command).toContain("--trust-model");
      expect(command).toContain("always");
    });

    it("should use regular GPG when no QUBES_ environment variables exist", () => {
      // Mock process.env to exclude all QUBES_ variables
      const originalEnv = process.env;
      const mockEnv = Object.keys(originalEnv)
        .filter((key) => !key.startsWith("QUBES_"))
        .reduce((env, key) => {
          env[key] = originalEnv[key];
          return env;
        }, {} as NodeJS.ProcessEnv);

      vi.stubGlobal("process", { ...process, env: mockEnv });

      // Reset singleton instance after mocking environment
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      (Crypto as any).instance = undefined;

      Crypto.initialize({});
      const crypto = Crypto.getInstance();

      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("gpg");
      expect(command).toContain("--trust-model");
      expect(command).toContain("always");

      // Restore original process.env
      vi.unstubAllGlobals();
    });

    it("should use custom homedir when provided", () => {
      Crypto.initialize({
        isQubes: false,
        gpgHomedir: "/custom/path",
      });
      const crypto = Crypto.getInstance();

      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("gpg");
      expect(command).toContain("--homedir");
      expect(command).toContain("/custom/path");
    });

    it("should override auto-detection when isQubes is explicitly set", () => {
      vi.stubEnv("QUBES_SOMETHING", "value");
      Crypto.initialize({ isQubes: false });
      const crypto = Crypto.getInstance();

      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("gpg");
    });
  });

  describe("getInstance", () => {
    beforeEach(() => {
      // Reset singleton instance for testing
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      (Crypto as any).instance = undefined;
    });

    it("should return null when not initialized", () => {
      expect(Crypto.getInstance()).toBe(null);
    });

    it("should return instance when initialized with config", () => {
      Crypto.initialize({ isQubes: false });
      expect(Crypto.getInstance()).not.toBe(null);
    });

    it("should return instance when initialized with empty config", () => {
      Crypto.initialize({});
      expect(Crypto.getInstance()).not.toBe(null);
    });
  });

  describe("readGzipHeaderFilename", () => {
    let crypto: Crypto;

    beforeEach(() => {
      // Reset singleton instance for testing
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      (Crypto as any).instance = undefined;
      Crypto.initialize({});
      crypto = Crypto.getInstance()!;
    });

    it("should extract filename from gzip header", () => {
      const filename = "test-file.txt";
      const gzipHeader = Buffer.from([
        0x1f,
        0x8b, // gzip magic
        0x08, // compression method
        0x08, // flags (FNAME bit set)
        0x00,
        0x00,
        0x00,
        0x00, // mtime
        0x00, // extra flags
        0x03, // OS
        ...Buffer.from(filename),
        0x00, // filename + null terminator
      ]);

      const result = (
        crypto as unknown as CryptoWithPrivateMethods
      ).readGzipHeaderFilename(gzipHeader);
      expect(result?.path).toBe(filename);
    });

    it("should return empty string when no filename in header", () => {
      const gzipHeader = Buffer.from([
        0x1f,
        0x8b, // gzip magic
        0x08, // compression method
        0x00, // flags (no FNAME bit)
        0x00,
        0x00,
        0x00,
        0x00, // mtime
        0x00, // extra flags
        0x03, // OS
      ]);

      const result = (
        crypto as unknown as CryptoWithPrivateMethods
      ).readGzipHeaderFilename(gzipHeader);
      expect(result).toBe(null);
    });

    it("should throw error for invalid gzip magic number", () => {
      const invalidHeader = Buffer.from([
        0x00,
        0x00,
        0x08,
        0x00, // Invalid magic + method
        0x00,
        0x00,
        0x00,
        0x00, // mtime
        0x00,
        0x03, // extra flags + OS (make it 10 bytes minimum)
      ]);

      expect(() => {
        (crypto as unknown as CryptoWithPrivateMethods).readGzipHeaderFilename(
          invalidHeader,
        );
      }).toThrow("Not a gzipped file");
    });

    it("should throw error for unknown compression method", () => {
      const invalidHeader = Buffer.from([
        0x1f,
        0x8b, // gzip magic
        0x07, // invalid compression method
        0x00, // flags
        0x00,
        0x00,
        0x00,
        0x00, // mtime
        0x00, // extra flags
        0x03, // OS
      ]);

      expect(() => {
        (crypto as unknown as CryptoWithPrivateMethods).readGzipHeaderFilename(
          invalidHeader,
        );
      }).toThrow("Unknown compression method");
    });
  });

  describe("CryptoError", () => {
    it("should create error with message and cause", () => {
      const cause = new Error("Original error");
      const cryptoError = new CryptoError("Crypto operation failed", cause);

      expect(cryptoError.message).toBe("Crypto operation failed");
      expect(cryptoError.cause).toBe(cause);
      expect(cryptoError.name).toBe("CryptoError");
    });
  });
});
