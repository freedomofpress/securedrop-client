import { describe, it, expect, vi, afterEach } from "vitest";
import { Config } from "./config";

import path from "path";
import os from "os";

describe("Config", () => {
  afterEach(() => {
    vi.restoreAllMocks();
    vi.unstubAllEnvs();
  });

  it("loads config from environment", () => {
    vi.stubEnv("SD_SUBMISSION_PUBKEY_PATH", "/home/.config/some-pubkey");
    const config = Config.load(true);
    expect(config.is_qubes).toBe(false);
    expect(config.journalist_public_key_path).toBe("/home/.config/some-pubkey");
  });

  it("returns default if environment variable is missing", () => {
    const config = Config.load(true);
    expect(config.journalist_public_key_path).toBe(
      path.join(os.homedir(), ".config", "SecureDrop", "public.key"),
    );
  });

  it("detectQubes returns true if QUBES_ env var exists", () => {
    const config = Config.load(false); // detectQubes should be false
    expect(config.is_qubes).toBe(false);

    vi.stubEnv("QUBES_TEST", "1");
    const configQubes = Config.load(false); // triggers detectQubes
    expect(configQubes.is_qubes).toBe(true);
  });
});
