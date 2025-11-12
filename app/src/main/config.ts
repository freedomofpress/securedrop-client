import path from "path";
import os from "os";

/**
 * Config loads configuration at runtime from QubesDB (if available),
 * falling back to the environment in non-Qubes mode
 */
export class Config {
  // Configuration variables
  journalist_public_key_path!: string;
  is_qubes!: boolean;

  public static load(noQubes: boolean): Config {
    const isQubes = noQubes ? !noQubes : detectQubes();
    console.log("Loading with isQubes: ", isQubes);
    return {
      journalist_public_key_path: tryReadEnvironment(
        "SD_SUBMISSION_PUBKEY_PATH",
        path.join(os.homedir(), ".config", "SecureDrop", "public.key"),
      ),
      is_qubes: isQubes,
    };
  }
}

// Attempts to read configuration from the environment, falling back to
// the default value
function tryReadEnvironment(key: string, defaultVal: string): string {
  return readEnvironment(key) ?? defaultVal;
}

function detectQubes(): boolean {
  return Object.keys(process.env).some((key) => key.startsWith("QUBES_"));
}

function readEnvironment(key: string): string | undefined {
  return import.meta.env[key];
}
