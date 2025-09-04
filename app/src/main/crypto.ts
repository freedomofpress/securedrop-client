import { spawn } from "child_process";
import { createGunzip } from "zlib";
import { pipeline } from "stream/promises";
import { Readable } from "stream";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";

export interface CryptoConfig {
  isQubes?: boolean; // Auto-detect if not provided
  gpgHomedir?: string;
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

  private constructor(config: CryptoConfig = {}) {
    this.isQubes = config.isQubes ?? this.detectQubes();
    this.gpgHomedir = config.gpgHomedir;
  }

  /**
   * Get singleton instance of Crypto
   */
  public static getInstance(config: CryptoConfig = {}): Crypto {
    if (!Crypto.instance) {
      Crypto.instance = new Crypto(config);
    }
    return Crypto.instance;
  }

  /**
   * Detect if running in Qubes OS by checking for QUBES_* environment variables
   */
  private detectQubes(): boolean {
    return Object.keys(process.env).some((key) => key.startsWith("QUBES_"));
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
   * Decrypt a message from encrypted buffer content
   * @param encryptedContent - The encrypted message content
   * @returns Promise<string> - The decrypted and decompressed plaintext
   */
  async decryptMessage(encryptedContent: Buffer): Promise<string> {
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt");

    return new Promise((resolve, reject) => {
      const gpgProcess = spawn(cmd[0], cmd.slice(1), {
        stdio: ["pipe", "pipe", "pipe"],
      });

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

        try {
          // Decompress the decrypted content
          const decompressed = await this.decompressGzip(stdout);
          resolve(decompressed);
        } catch (error) {
          reject(
            new CryptoError(
              "Failed to decompress decrypted message",
              error instanceof Error ? error : new Error(String(error)),
            ),
          );
        }
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
   * @returns Promise with path to decrypted file and original filename
   */
  async decryptFile(
    filepath: string,
  ): Promise<{ filePath: string; filename: string }> {
    const cmd = this.getGpgCommand();
    cmd.push("--decrypt", filepath);

    return new Promise((resolve, reject) => {
      // Create temporary file for GPG output (similar to legacy client's approach)
      const tempDir = os.tmpdir();
      const tempGpgOutput = path.join(
        tempDir,
        `securedrop-gpg-${Date.now()}-${Math.random().toString(36).slice(2)}`,
      );

      const gpgOutputFile = fs.createWriteStream(tempGpgOutput);
      let stderr = Buffer.alloc(0);

      const gpgProcess = spawn(cmd[0], cmd.slice(1), {
        stdio: ["pipe", "pipe", "pipe"],
      });

      // Stream GPG output directly to temporary file (no memory accumulation)
      gpgProcess.stdout.pipe(gpgOutputFile);

      // Collect stderr (error messages)
      gpgProcess.stderr.on("data", (chunk) => {
        stderr = Buffer.concat([stderr, chunk]);
      });

      gpgProcess.on("close", async (code) => {
        gpgOutputFile.end();

        if (code !== 0) {
          // Clean up temp file on error
          fs.unlink(tempGpgOutput, () => {});
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
          const outputPath = path.join(
            tempDir,
            `securedrop-decrypted-${Date.now()}-${finalFilename}`,
          );

          // Stream decompress the gzipped content to final file
          await this.streamDecompressGzipFile(tempGpgOutput, outputPath);

          // Clean up temporary GPG output file
          fs.unlink(tempGpgOutput, () => {});

          resolve({ filePath: outputPath, filename: finalFilename });
        } catch (error) {
          // Clean up temp files on error
          fs.unlink(tempGpgOutput, () => {});
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
        fs.unlink(tempGpgOutput, () => {});
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
   * Decompress gzip content and return as string
   */
  private async decompressGzip(compressedData: Buffer): Promise<string> {
    const readable = Readable.from([compressedData]);
    const gunzip = createGunzip();

    const chunks: Buffer[] = [];

    await pipeline(readable, gunzip, async function* (source) {
      for await (const chunk of source) {
        chunks.push(chunk);
        yield chunk;
      }
    });

    return Buffer.concat(chunks).toString("utf8");
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
  ): Promise<string> {
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
  private readGzipHeaderFilename(data: Buffer): string {
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

      return data.subarray(filenameStart, filenameEnd).toString("utf8");
    }

    return ""; // No filename in header
  }
}
