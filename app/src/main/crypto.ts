import { spawn } from "child_process";
import { createGunzip } from "zlib";
import { pipeline } from "stream/promises";

import * as openpgp from "openpgp";
import * as fs from "fs";
import * as path from "path";
import { PathBuilder, Storage, UnsafePathComponent } from "./storage";

export interface CryptoConfig {
  isQubes: boolean;
  gpgHomedir?: string;
  qubesGpgDomain?: string;
  submissionKeyFingerprint: string;
}

export class CryptoError extends Error {
  constructor(
    message: string,
    public readonly cause?: Error,
  ) {
    super(message);
    this.name = "CryptoError";
  }
}

export class Crypto {
  private static instance: Crypto;
  private isQubes: boolean;
  private gpgHomedir?: string;
  private qubesGpgDomain?: string;
  private submissionKeyFingerprint: string;
  private submissionKey?: string;

  private constructor(config: CryptoConfig) {
    this.isQubes = config.isQubes;
    this.gpgHomedir = config.gpgHomedir;
    this.qubesGpgDomain = config.qubesGpgDomain;
    this.submissionKeyFingerprint = config.submissionKeyFingerprint;
  }

  /**
   * Initialize global crypto configuration (must be called before getInstance)
   */
  public static initialize(config: CryptoConfig): Crypto {
    if (Crypto.instance) {
      throw new Error(
        "Crypto already initialized: cannot initialize twice. Call initialize() before getInstance().",
      );
    }

    Crypto.instance = new Crypto(config);
    return Crypto.instance;
  }

  /**
   * Get singleton instance of Crypto
   */
  public static getInstance(): Crypto | null {
    if (!Crypto.instance) {
      return null;
    }
    return Crypto.instance;
  }

  /**
   * Get the base GPG command based on environment (Qubes vs dev)
   */
  private getGpgCommand(): string[] {
    if (this.isQubes) {
      return ["qubes-gpg-client", "--trust-model", "always"];
    } else {
      const cmd = ["gpg", "--trust-model", "always"];
      if (this.gpgHomedir) {
        cmd.push("--homedir", this.gpgHomedir);
      }
      return cmd;
    }
  }

  /**
   * Get the environment for running GPG
   */
  private getGpgEnv(): NodeJS.ProcessEnv {
    if (this.isQubes && this.qubesGpgDomain) {
      return { ...process.env, QUBES_GPG_DOMAIN: this.qubesGpgDomain };
    }
    return process.env;
  }

  /**
   * Lazily get the public part of the submission key
   */
  async getSubmissionKey(): Promise<string> {
    if (!this.submissionKey) {
      this.submissionKey = await this.exportSubmissionKey();
    }
    return this.submissionKey;
  }

  /**
   * Internal method to export the public part of the submission key
   * from sd-gpg by using qubes-split-gpg
   */
  async exportSubmissionKey(): Promise<string> {
    const cmd = this.getGpgCommand();
    cmd.push("--export", "--armor", this.submissionKeyFingerprint);

    return new Promise((resolve, reject) => {
      const process = spawn(cmd[0], cmd.slice(1), { env: this.getGpgEnv() });
      let stdout = "";
      let stderr = "";

      process.stdout.on("data", (data) => {
        stdout += data.toString();
      });

      process.stderr.on("data", (data) => {
        stderr += data.toString();
      });

      process.on("error", (err) => {
        reject(err);
      });

      process.on("close", (code, signal) => {
        if (signal) {
          reject(new Error(`Process terminated with signal ${signal}`));
        } else if (code !== 0) {
          reject(
            new Error(`Process exited with non-zero code ${code}: ${stderr}`),
          );
        } else if (!stdout.trim()) {
          reject(
            new Error(
              `Failed to export key ${this.submissionKeyFingerprint}: Key not found or export returned empty result`,
            ),
          );
        } else {
          resolve(stdout);
        }
      });
    });
  }

  /**
   * Decrypt a message from encrypted buffer content
   * Messages are not gzipped, so no decompression is needed (unlike files)
   * @param encryptedContent - The encrypted message content
   * @returns Promise<string> - The decrypted plaintext
   */
  async decryptMessage(encryptedContent: Buffer): Promise<string> {
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt");

    return new Promise((resolve, reject) => {
      const gpgProcess = spawn(cmd[0], cmd.slice(1), { env: this.getGpgEnv() });

      let stdout = Buffer.alloc(0);
      let stderr = Buffer.alloc(0);

      // Write encrypted content to GPG stdin
      gpgProcess.stdin.write(encryptedContent);
      gpgProcess.stdin.end();

      // Collect stdout (decrypted content)
      gpgProcess.stdout.on("data", (chunk) => {
        stdout = Buffer.concat([stdout, chunk]);
      });

      // Collect stderr (error messages)
      gpgProcess.stderr.on("data", (chunk) => {
        stderr = Buffer.concat([stderr, chunk]);
      });

      gpgProcess.on("close", async (code) => {
        if (code !== 0) {
          const errorMessage = stderr.toString("utf8");
          reject(
            new CryptoError(
              `GPG decryption failed (exit code ${code}): ${errorMessage}`,
            ),
          );
          return;
        }

        // Messages are not gzipped, so return the decrypted content directly as string
        resolve(stdout.toString("utf8"));
      });

      gpgProcess.on("error", (error) => {
        reject(
          new CryptoError(
            `Failed to start GPG process: ${error.message}`,
            error,
          ),
        );
      });
    });
  }

  /**
   * Decrypt a file and return the path to the decrypted file with original filename
   * Uses streaming approach to handle large files efficiently (similar to legacy client)
   * @param filepath - Path to the encrypted file
   * @returns Promise with path to decrypted file
   */
  async decryptFile(
    storage: Storage,
    itemDirectory: PathBuilder,
    filepath: string,
  ): Promise<string> {
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt", filepath);

    return new Promise((resolve, reject) => {
      // Create temporary directory for this operation
      const tempDir = storage.createTempDir("securedrop-decrypt-");
      const tempGpgOutput = tempDir.join("decrypted.gz");

      const gpgOutputFile = fs.createWriteStream(tempGpgOutput);
      let stderr = Buffer.alloc(0);

      const gpgProcess = spawn(cmd[0], cmd.slice(1), { env: this.getGpgEnv() });

      // Stream GPG output directly to temporary file (no memory accumulation)
      gpgProcess.stdout.pipe(gpgOutputFile);

      // Collect stderr (error messages)
      gpgProcess.stderr.on("data", (chunk) => {
        stderr = Buffer.concat([stderr, chunk]);
      });

      gpgProcess.on("close", async (code) => {
        gpgOutputFile.end();

        if (code !== 0) {
          // Clean up temp directory on error
          fs.rmSync(tempDir.path, { recursive: true, force: true });
          const errorMessage = stderr.toString("utf8");
          reject(
            new CryptoError(
              `GPG file decryption failed (exit code ${code}): ${errorMessage}`,
            ),
          );
          return;
        }

        try {
          // Extract original filename from gzip header
          const originalFilename =
            await this.readGzipHeaderFilenameFromFile(tempGpgOutput);

          // Create final output file path
          const finalFilename =
            originalFilename || path.basename(filepath, ".gpg");
          const finalAbsolutePath = itemDirectory.join(finalFilename);

          // Stream decompress the gzipped content to final file
          await this.streamDecompressGzipFile(tempGpgOutput, finalAbsolutePath);

          // Clean up temporary GPG output file
          fs.unlink(tempGpgOutput, () => {});

          resolve(finalAbsolutePath);
        } catch (error) {
          // Clean up temp directory on error
          fs.rmSync(tempDir.path, { recursive: true, force: true });
          reject(
            new CryptoError(
              "Failed to decompress decrypted file",
              error instanceof Error ? error : new Error(String(error)),
            ),
          );
        }
      });

      gpgProcess.on("error", (error) => {
        gpgOutputFile.destroy();
        fs.rmSync(tempDir.path, { recursive: true, force: true });
        reject(
          new CryptoError(
            `Failed to start GPG process for file decryption: ${error.message}`,
            error,
          ),
        );
      });
    });
  }

  /**
   * Encrypts a message to a source given the source public key. Message
   * will be encrypted to source and journalist public keys.
   * @param plaintext - The message plaintext
   * @param sourcePublicKey - Source PGP public key
   * @returns Promise<string> - The encrypted ciphertext
   */
  async encryptSourceMessage(
    plaintext: string,
    sourcePublicKey: string,
  ): Promise<string> {
    return encryptMessage(plaintext, [
      sourcePublicKey,
      await this.getSubmissionKey(),
    ]);
  }

  /**
   * Stream decompress a gzip file to another file (memory efficient)
   * Similar to legacy client's safe_copyfileobj approach
   */
  private async streamDecompressGzipFile(
    gzipFilePath: string,
    outputPath: string,
  ): Promise<void> {
    const readStream = fs.createReadStream(gzipFilePath);
    const writeStream = fs.createWriteStream(outputPath);
    const gunzip = createGunzip();

    await pipeline(readStream, gunzip, writeStream);
  }

  /**
   * Read gzip header filename from a file on disk (without loading entire file)
   */
  private async readGzipHeaderFilenameFromFile(
    filePath: string,
  ): Promise<UnsafePathComponent | null> {
    return new Promise((resolve, reject) => {
      const readStream = fs.createReadStream(filePath, { start: 0, end: 1023 }); // Read first 1KB for header
      let headerData = Buffer.alloc(0);

      readStream.on("data", (chunk: string | Buffer) => {
        const bufferChunk = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
        headerData = Buffer.concat([headerData, bufferChunk]);
      });

      readStream.on("end", () => {
        try {
          const filename = this.readGzipHeaderFilename(headerData);
          resolve(filename);
        } catch (error) {
          reject(error);
        }
      });

      readStream.on("error", reject);
    });
  }

  /**
   * Extract original filename from gzip header
   */
  private readGzipHeaderFilename(data: Buffer): UnsafePathComponent | null {
    if (data.length < 10) {
      throw new Error("Data too short to be a valid gzip file");
    }

    // Check gzip magic number
    const GZIP_MAGIC = Buffer.from([0x1f, 0x8b]);
    if (!data.subarray(0, 2).equals(GZIP_MAGIC)) {
      throw new Error(
        `Not a gzipped file (got ${data.subarray(0, 2).toString("hex")})`,
      );
    }

    // Check compression method
    const compressionMethod = data[2];
    if (compressionMethod !== 8) {
      throw new Error("Unknown compression method");
    }

    // Get flags
    const flags = data[3];
    const FEXTRA = 4; // Extra fields present
    const FNAME = 8; // Filename present

    let offset = 10; // Skip fixed header

    // Skip extra fields if present
    if (flags & FEXTRA) {
      if (offset + 2 > data.length) {
        throw new Error("Incomplete gzip header");
      }
      const extraLen = data.readUInt16LE(offset);
      offset += 2 + extraLen;
    }

    // Read filename if present
    if (flags & FNAME) {
      const filenameStart = offset;
      let filenameEnd = filenameStart;

      // Find null terminator
      while (filenameEnd < data.length && data[filenameEnd] !== 0) {
        filenameEnd++;
      }

      if (filenameEnd >= data.length) {
        throw new Error("Filename in gzip header not null-terminated");
      }

      const filename = data
        .subarray(filenameStart, filenameEnd)
        .toString("utf8");
      return new UnsafePathComponent(filename);
    }

    return null; // No filename in header
  }
}

/**
 * Encrypts a message to a source to the specified recipients
 * @param plaintext - The message plaintext
 * @param recipientPublicKeys - ASCII-encoded armored public keys for message recipients
 * @returns Promise<string> - The encrypted ciphertext
 */
export async function encryptMessage(
  plaintext: string,
  recipientPublicKeys: string[],
): Promise<string> {
  const publicKeys = await Promise.all(
    recipientPublicKeys.map((recipient) =>
      openpgp.readKey({ armoredKey: recipient }),
    ),
  );

  return await openpgp.encrypt({
    message: await openpgp.createMessage({ text: plaintext }),
    encryptionKeys: publicKeys,
  });
}
