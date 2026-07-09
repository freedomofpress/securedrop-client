import { describe, it, expect, beforeEach, vi, afterEach } from "vitest";
import { EventEmitter } from "events";
import { PassThrough } from "stream";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { Crypto, CryptoError, isPgpEncrypted } from "../crypto";
import { UnsafePathComponent } from "../storage";

const spawnMock = vi.hoisted(() => vi.fn());
vi.mock("child_process", async (importOriginal) => {
  const actual = await importOriginal<typeof import("child_process")>();
  return { ...actual, spawn: spawnMock };
});

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
      (Crypto as any).instance = undefined;
    });

    it("should use custom homedir when provided", () => {
      const crypto = Crypto.initialize({
        submissionKeyFingerprint: "",
        isQubes: false,
        gpgHomedir: "/custom/path",
      });

      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("gpg");
      expect(command).toContain("--homedir");
      expect(command).toContain("/custom/path");
    });

    it("should override auto-detection when isQubes is explicitly set", () => {
      vi.stubEnv("QUBES_SOMETHING", "value");
      const crypto = Crypto.initialize({
        isQubes: false,
        submissionKeyFingerprint: "",
      });

      const command = (
        crypto as unknown as CryptoWithPrivateMethods
      ).getGpgCommand();
      expect(command[0]).toBe("gpg");
    });
  });

  describe("getInstance", () => {
    beforeEach(() => {
      // Reset singleton instance for testing
      (Crypto as any).instance = undefined;
    });

    it("should return null when not initialized", () => {
      expect(Crypto.getInstance()).toBe(null);
    });

    it("should return instance when initialized with config", () => {
      Crypto.initialize({ isQubes: false, submissionKeyFingerprint: "" });
      expect(Crypto.getInstance()).not.toBe(null);
    });

    it("should return instance when initialized with empty config", () => {
      Crypto.initialize({ submissionKeyFingerprint: "", isQubes: false });
      expect(Crypto.getInstance()).not.toBe(null);
    });
  });

  describe("readGzipHeaderFilename", () => {
    let crypto: Crypto;

    beforeEach(() => {
      // Reset singleton instance for testing
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        submissionKeyFingerprint: "",
        isQubes: false,
      });
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

    it("should return null when gzip header filename is empty string", () => {
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
        0x00, // empty filename (just the null terminator)
      ]);

      const result = (
        crypto as unknown as CryptoWithPrivateMethods
      ).readGzipHeaderFilename(gzipHeader);
      expect(result).toBe(null);
    });

    it("should return null when no filename in header", () => {
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

  describe("isPgpEncrypted", () => {
    it("returns false for an empty buffer", () => {
      expect(isPgpEncrypted(Buffer.alloc(0))).toBe(false);
    });

    it("returns false for plaintext", () => {
      expect(isPgpEncrypted(Buffer.from("hello world"))).toBe(false);
    });

    it("returns true for an ASCII-armored PGP message", () => {
      expect(
        isPgpEncrypted(Buffer.from("-----BEGIN PGP MESSAGE-----\n...")),
      ).toBe(true);
    });

    it("returns false for an ASCII-armored PGP signed message (not encrypted)", () => {
      expect(
        isPgpEncrypted(
          Buffer.from("-----BEGIN PGP SIGNED MESSAGE-----\nHash: SHA256\n..."),
        ),
      ).toBe(false);
    });

    it("returns true for a binary OpenPGP new-format Public-Key ESK packet (tag 1)", () => {
      // New format: bit7=1, bit6=1, tag=1 → 0xC1
      expect(isPgpEncrypted(Buffer.from([0xc1, 0x00]))).toBe(true);
    });

    it("returns true for a binary OpenPGP new-format Symmetric-Key ESK packet (tag 3)", () => {
      // New format: bit7=1, bit6=1, tag=3 → 0xC3
      expect(isPgpEncrypted(Buffer.from([0xc3, 0x00]))).toBe(true);
    });

    it("returns true for a binary OpenPGP old-format Public-Key ESK packet (tag 1)", () => {
      // Old format: bit7=1, bit6=0, tag=1 in bits 5-2, length-type=0 → 0x84
      expect(isPgpEncrypted(Buffer.from([0x84, 0x00]))).toBe(true);
    });

    it("returns true for a binary OpenPGP old-format Symmetric-Key ESK packet (tag 3)", () => {
      // Old format: bit7=1, bit6=0, tag=3 in bits 5-2, length-type=0 → 0x8c
      expect(isPgpEncrypted(Buffer.from([0x8c, 0x00]))).toBe(true);
    });

    it("returns false for a binary OpenPGP packet with a non-ESK tag (e.g. tag 11 = literal data)", () => {
      // New format: bit7=1, bit6=1, tag=11 → 0xCB
      expect(isPgpEncrypted(Buffer.from([0xcb, 0x00]))).toBe(false);
    });

    it("returns false when bit 7 is not set", () => {
      expect(isPgpEncrypted(Buffer.from([0x01, 0x00]))).toBe(false);
    });
  });

  describe("decryptRawFile (inner layer of double-encrypted files)", () => {
    let crypto: Crypto;
    let tmpDir: string;
    let inputPath: string;
    let outputPath: string;

    // Minimal stand-in for a spawned gpg process: emits the given stdout
    // and stderr, then closes with the given exit code.
    function fakeGpgProcess(options: {
      stdoutData?: Buffer;
      stderrData?: Buffer;
      code?: number;
    }) {
      const proc = new EventEmitter() as any;
      proc.stdout = new PassThrough();
      proc.stderr = new PassThrough();
      proc.stdin = new PassThrough();
      proc.kill = vi.fn();
      setImmediate(() => {
        if (options.stderrData) {
          proc.stderr.write(options.stderrData);
        }
        proc.stdout.end(options.stdoutData ?? Buffer.alloc(0));
        proc.stderr.end();
        setImmediate(() => proc.emit("close", options.code ?? 0, null));
      });
      return proc;
    }

    beforeEach(() => {
      (Crypto as any).instance = undefined;
      crypto = Crypto.initialize({
        isQubes: true,
        qubesGpgDomain: "sd-gpg",
        submissionKeyFingerprint: "",
      });
      tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "crypto-unit-test-"));
      inputPath = path.join(tmpDir, "document.txt.gpg");
      outputPath = path.join(tmpDir, "document.txt");
      fs.writeFileSync(inputPath, "ciphertext");
    });

    afterEach(() => {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    });

    it("streams plaintext from stdout instead of passing --output, which qubes-gpg-client rejects", async () => {
      const plaintext = Buffer.from("inner plaintext");
      spawnMock.mockImplementation(() =>
        fakeGpgProcess({ stdoutData: plaintext }),
      );

      await (crypto as any).decryptRawFile(inputPath, outputPath);

      expect(spawnMock).toHaveBeenCalledTimes(1);
      const [command, args] = spawnMock.mock.calls[0];
      expect(command).toBe("qubes-gpg-client");
      // split-gpg only permits `--output -`, so the plaintext must be
      // streamed from stdout rather than written by gpg itself
      expect(args).not.toContain("--output");
      expect(args).toContain(inputPath);
      expect(fs.readFileSync(outputPath)).toEqual(plaintext);
    });

    it("removes partial output and rejects when gpg exits non-zero", async () => {
      spawnMock.mockImplementation(() =>
        fakeGpgProcess({
          stdoutData: Buffer.from("partial output"),
          stderrData: Buffer.from("gpg: decryption failed: No secret key\n"),
          code: 2,
        }),
      );

      await expect(
        (crypto as any).decryptRawFile(inputPath, outputPath),
      ).rejects.toThrow(/Inner GPG decryption failed \(exit code 2\)/);
      expect(fs.existsSync(outputPath)).toBe(false);
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
