import { describe, it, expect, vi, afterEach } from "vitest";
import { Config } from "./config";
import child_process from "node:child_process";

describe("Config", () => {
  afterEach(() => {
    vi.restoreAllMocks();
    vi.unstubAllEnvs();
  });

  it("loads config from environment when not in Qubes mode", () => {
    vi.stubEnv("SD_SUBMISSION_PUBKEY", "env-pubkey");
    const config = Config.load(true);
    expect(config.is_qubes).toBe(false);
    expect(config.journalist_public_key).toBe("env-pubkey");
  });

  it("throws error if required environment variable is missing", () => {
    expect(() => Config.load(false)).toThrow(
      /unable to read config value for required variable SD_SUBMISSION_PUBKEY/,
    );
  });

  it("loads config from QubesDB when in Qubes mode", () => {
    vi.stubEnv("QUBES_TEST", "1");
    const qubesValue = "qubes-pubkey";
    const execSyncMock = vi
      .spyOn(child_process, "execSync")
      .mockReturnValue(qubesValue);

    const config = Config.load(false);
    expect(config.is_qubes).toBe(true);
    expect(config.journalist_public_key).toBe(qubesValue);
    expect(execSyncMock).toHaveBeenCalledWith(
      "qubesdb-get /vm-config/SD_SUBMISSION_PUBKEY",
      { encoding: "utf8" },
    );
  });

  it("throws error if QubesDB variable is missing", () => {
    vi.stubEnv("QUBES_TEST", "1");
    vi.spyOn(child_process, "execSync").mockRejectedValue("not found");
    expect(() => Config.load(false)).toThrow(
      /unable to read config value for required variable SD_SUBMISSION_PUBKEY/,
    );
  });

  it("detectQubes returns true if QUBES_ env var exists", () => {
    vi.stubEnv("SD_SUBMISSION_PUBKEY", "some-pubkey");
    const config = Config.load(false); // detectQubes should be false
    expect(config.is_qubes).toBe(false);

    vi.stubEnv("QUBES_TEST", "1");
    vi.spyOn(child_process, "execSync").mockReturnValue("some-pubkey");
    const configQubes = Config.load(false); // triggers detectQubes
    expect(configQubes.is_qubes).toBe(true);
  });
});
