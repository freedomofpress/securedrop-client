import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";
import { Config } from "./config";

// Mock child_process at the module level
vi.mock("child_process", () => ({
  spawnSync: vi.fn(),
}));

import { spawnSync } from "child_process";

const FINGERPRINT = "0123456789ABCDEF0123456789ABCDEF01234567";

describe("Config", () => {
  beforeEach(() => {
    // Clear all environment variables that might affect tests
    delete process.env.QUBES_TEST;
    delete (import.meta.env as any).SD_SUBMISSION_KEY_FPR;
    delete (import.meta.env as any).QUBES_ENV_SOURCED;
    delete (import.meta.env as any).QUBES_GPG_DOMAIN;
    delete (import.meta.env as any).GNUPGHOME;
    // Clear mock state
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
    vi.unstubAllEnvs();
  });

  describe("Non-Qubes mode", () => {
    it("loads required config from import.meta.env", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = FINGERPRINT;
      (import.meta.env as any).QUBES_GPG_DOMAIN = "my-gpg-domain";

      const config = Config.load(true);

      expect(config.is_qubes).toBe(false);
      expect(config.sd_submission_key_fpr).toBe(FINGERPRINT);
      expect(config.qubes_gpg_domain).toBe("my-gpg-domain");
    });

    it("uses default values for optional config", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = FINGERPRINT;

      const config = Config.load(true);

      expect(config.qubes_gpg_domain).toBe("");
    });

    it("loads GNUPGHOME from environment for development", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = FINGERPRINT;
      (import.meta.env as any).GNUPGHOME = "/custom/gnupg";

      const config = Config.load(true);

      expect(config.gnupghome).toBe("/custom/gnupg");
    });

    it("throws error if required config is missing", () => {
      expect(() => Config.load(true)).toThrow(
        "Missing configuration value: SD_SUBMISSION_KEY_FPR",
      );
    });

    it("normalizes fingerprint case and spacing", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR =
        "0123 4567 89ab cdef 0123 4567 89ab cdef 0123 4567";

      expect(Config.load(true).sd_submission_key_fpr).toBe(FINGERPRINT);
    });

    it("rejects a 16-character key ID", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = "89ABCDEF01234567";

      expect(() => Config.load(true)).toThrow(
        "SD_SUBMISSION_KEY_FPR must be a full 40-character fingerprint",
      );
    });
  });

  describe("Qubes mode", () => {
    it("loads config from QubesDB", () => {
      vi.mocked(spawnSync).mockImplementation((_command, args) => {
        const key = args?.[0] as string;
        if (key === "/vm-config/SD_SUBMISSION_KEY_FPR") {
          return {
            status: 0,
            stdout: `${FINGERPRINT}\n`,
            stderr: "",
            signal: null,
            error: undefined,
          } as any;
        }
        if (key === "/vm-config/QUBES_GPG_DOMAIN") {
          return {
            status: 0,
            stdout: "gpg-domain\n",
            stderr: "",
            signal: null,
            error: undefined,
          } as any;
        }
        return {
          status: 2,
          stdout: "",
          stderr: "",
          signal: null,
          error: undefined,
        } as any;
      });

      vi.stubEnv("QUBES_TEST", "1");
      const config = Config.load(false);

      expect(config.is_qubes).toBe(true);
      expect(config.sd_submission_key_fpr).toBe(FINGERPRINT);
      expect(config.qubes_gpg_domain).toBe("gpg-domain");
    });

    it("uses default values when QubesDB returns status 2", () => {
      vi.mocked(spawnSync).mockImplementation((_command, args) => {
        const key = args?.[0] as string;
        if (key === "/vm-config/SD_SUBMISSION_KEY_FPR") {
          return {
            status: 0,
            stdout: `${FINGERPRINT}\n`,
            stderr: "",
            signal: null,
            error: undefined,
          } as any;
        }
        // All other keys return status 2 (not found)
        return {
          status: 2,
          stdout: "",
          stderr: "",
          signal: null,
          error: undefined,
        } as any;
      });

      vi.stubEnv("QUBES_TEST", "1");
      const config = Config.load(false);

      expect(config.sd_submission_key_fpr).toBe(FINGERPRINT);
      expect(config.qubes_gpg_domain).toBe("");
    });

    it("throws error if required config missing from QubesDB", () => {
      vi.mocked(spawnSync).mockReturnValue({
        status: 2,
        stdout: "",
        stderr: "",
        signal: null,
        error: undefined,
      } as any);

      vi.stubEnv("QUBES_TEST", "1");

      expect(() => Config.load(false)).toThrow(
        "Missing configuration value: SD_SUBMISSION_KEY_FPR",
      );
    });

    it("throws error on qubesdb-read spawn error", () => {
      vi.mocked(spawnSync).mockReturnValue({
        status: null,
        stdout: "",
        stderr: "",
        signal: null,
        error: new Error("spawn failed"),
      } as any);

      vi.stubEnv("QUBES_TEST", "1");

      expect(() => Config.load(false)).toThrow("spawn failed");
    });

    it("throws error on qubesdb-read timeout", () => {
      vi.mocked(spawnSync).mockReturnValue({
        status: null,
        stdout: "",
        stderr: "",
        signal: "SIGTERM",
        error: undefined,
      } as any);

      vi.stubEnv("QUBES_TEST", "1");

      expect(() => Config.load(false)).toThrow(
        "Process terminated with signal SIGTERM",
      );
    });

    it("throws error on qubesdb-read non-zero exit code", () => {
      vi.mocked(spawnSync).mockReturnValue({
        status: 1,
        stdout: "",
        stderr: "error message",
        signal: null,
        error: undefined,
      } as any);

      vi.stubEnv("QUBES_TEST", "1");

      expect(() => Config.load(false)).toThrow(
        "Process exited with non-zero code 1: error message",
      );
    });
  });

  describe("Qubes detection", () => {
    it("detects Qubes when QUBES_ env var exists", () => {
      vi.mocked(spawnSync).mockImplementation((_command, args) => {
        const key = args?.[0] as string;
        if (key === "/vm-config/SD_SUBMISSION_KEY_FPR") {
          return {
            status: 0,
            stdout: `${FINGERPRINT}\n`,
            stderr: "",
            signal: null,
            error: undefined,
          } as any;
        }
        return {
          status: 2,
          stdout: "",
          stderr: "",
          signal: null,
          error: undefined,
        } as any;
      });

      vi.stubEnv("QUBES_TEST", "1");

      const config = Config.load(false);

      expect(config.is_qubes).toBe(true);
    });

    it("does not detect Qubes when no QUBES_ env vars exist", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = FINGERPRINT;

      const config = Config.load(false);

      expect(config.is_qubes).toBe(false);
    });

    it("respects noQubes parameter even with QUBES_ env var", () => {
      (import.meta.env as any).SD_SUBMISSION_KEY_FPR = FINGERPRINT;
      vi.stubEnv("QUBES_TEST", "1");

      const config = Config.load(true);

      expect(config.is_qubes).toBe(false);
    });
  });
});
