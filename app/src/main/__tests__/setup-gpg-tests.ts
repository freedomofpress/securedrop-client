/**
 * Test setup utilities for GPG-based crypto tests
 *
 * This file provides helper functions to set up isolated GPG environments
 * for testing crypto operations without affecting the system GPG keyring.
 */

import * as fs from "fs";
import * as path from "path";
import * as os from "os";
import { execSync } from "child_process";

export interface GpgTestEnvironment {
  homedir: string;
  cleanup: () => void;
  importKey: (keyContent: string) => string;
  listKeys: () => string[];
  createTestKey: (name: string, email: string) => string;
}

/**
 * Create an isolated GPG test environment
 */
export function createGpgTestEnvironment(): GpgTestEnvironment {
  const homedir = fs.mkdtempSync(
    path.join(os.tmpdir(), "securedrop-test-gpg-"),
  );

  // Initialize empty GPG homedir
  try {
    execSync(`gpg --homedir "${homedir}" --list-keys`, { stdio: "pipe" });
  } catch {
    // Expected to fail on first run, creates the homedir
  }

  const cleanup = () => {
    if (fs.existsSync(homedir)) {
      fs.rmSync(homedir, { recursive: true, force: true });
    }
  };

  const importKey = (keyContent: string): string => {
    try {
      execSync(`gpg --homedir "${homedir}" --batch --import --with-colons`, {
        input: keyContent,
        encoding: "utf8",
        stdio: "pipe",
      });

      // Extract key ID from import result
      const keyId = execSync(
        `gpg --homedir "${homedir}" --list-keys --with-colons | grep '^pub' | tail -1 | cut -d: -f5`,
        {
          encoding: "utf8",
        },
      ).trim();

      // Set ultimate trust
      if (keyId) {
        execSync(
          `gpg --homedir "${homedir}" --batch --command-fd 0 --edit-key ${keyId}`,
          {
            input: "trust\n5\ny\nquit\n",
            stdio: "pipe",
          },
        );
      }

      return keyId;
    } catch (error) {
      throw new Error(`Failed to import key: ${error}`);
    }
  };

  const listKeys = (): string[] => {
    try {
      const result = execSync(
        `gpg --homedir "${homedir}" --list-keys --with-colons | grep '^pub' | cut -d: -f5`,
        {
          encoding: "utf8",
        },
      );
      return result.trim().split("\n").filter(Boolean);
    } catch {
      return [];
    }
  };

  const createTestKey = (name: string, email: string): string => {
    const keyGenInput = `
Key-Type: RSA
Key-Length: 2048
Name-Real: ${name}
Name-Email: ${email}
Expire-Date: 0
%no-protection
%commit
`;

    execSync(`gpg --homedir "${homedir}" --batch --gen-key`, {
      input: keyGenInput,
      stdio: "pipe",
    });

    // Get the created key ID
    const keyId = execSync(
      `gpg --homedir "${homedir}" --list-keys --with-colons | grep '^pub' | tail -1 | cut -d: -f5`,
      {
        encoding: "utf8",
      },
    ).trim();

    return keyId;
  };

  return {
    homedir,
    cleanup,
    importKey,
    listKeys,
    createTestKey,
  };
}

/**
 * Create test encrypted content for testing
 */
export function createTestEncryptedContent(
  content: string,
  recipientKeyId: string,
  gpgHomedir: string,
  armor: boolean = true,
): Buffer {
  const armorFlag = armor ? "--armor" : "";
  const result = execSync(
    `gpg --homedir "${gpgHomedir}" --trust-model always --encrypt ${armorFlag} -r ${recipientKeyId}`,
    {
      input: content,
      stdio: "pipe",
    },
  );

  return Buffer.from(result);
}

/**
 * Create test gzipped and encrypted file for testing
 */
export function createTestEncryptedFile(
  content: string | Buffer,
  filename: string,
  recipientKeyId: string,
  gpgHomedir: string,
): { filePath: string; cleanup: () => void } {
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "crypto-file-test-"));
  const tempFile = path.join(tempDir, filename);

  // Write original file (handles both string and Buffer)
  fs.writeFileSync(tempFile, content);

  // Gzip the file
  const gzippedFile = `${tempFile}.gz`;
  execSync(`gzip -c "${tempFile}" > "${gzippedFile}"`);

  // Encrypt the gzipped file
  const encryptedFile = `${gzippedFile}.gpg`;
  execSync(
    `gpg --homedir "${gpgHomedir}" --trust-model always --encrypt -r ${recipientKeyId} --output "${encryptedFile}" "${gzippedFile}"`,
  );

  return {
    filePath: encryptedFile,
    cleanup: () => {
      if (fs.existsSync(tempDir)) {
        fs.rmSync(tempDir, { recursive: true, force: true });
      }
    },
  };
}

/**
 * Verify GPG is available on the system
 */
export function verifyGpgAvailable(): boolean {
  try {
    execSync("gpg --version", { stdio: "pipe" });
    return true;
  } catch {
    return false;
  }
}

/**
 * Read test key files from the test files directory
 */
export function loadTestKeys(testFilesDir: string): {
  publicKey?: string;
  privateKey?: string;
} {
  const pubKeyPath = path.join(testFilesDir, "test-key.gpg.pub.asc");
  const privKeyPath = path.join(testFilesDir, "securedrop.gpg.asc");

  let publicKey: string | undefined;
  let privateKey: string | undefined;

  try {
    if (fs.existsSync(pubKeyPath)) {
      publicKey = fs.readFileSync(pubKeyPath, "utf8");
    }
  } catch (error) {
    console.warn(`Could not read public key from ${pubKeyPath}:`, error);
  }

  try {
    if (fs.existsSync(privKeyPath)) {
      privateKey = fs.readFileSync(privKeyPath, "utf8");
    }
  } catch (error) {
    console.warn(`Could not read private key from ${privKeyPath}:`, error);
  }

  return { publicKey, privateKey };
}
