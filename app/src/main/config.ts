import { spawnSync } from "child_process";

/**
 * Config loads configuration at runtime from QubesDB (if available),
 * falling back to the environment in non-Qubes mode
 */
export class Config {
  // Configuration variables
  readonly gnupghome?: string;
  readonly is_qubes!: boolean;
  readonly qubes_gpg_domain!: string;
  readonly sd_submission_key_fpr!: string;

  public static load(noQubes: boolean): Config {
    const isQubes = noQubes ? !noQubes : detectQubes();
    console.log("Loading with isQubes: ", isQubes);
    return {
      qubes_gpg_domain: read(isQubes, "QUBES_GPG_DOMAIN", ""),
      sd_submission_key_fpr: read(isQubes, "SD_SUBMISSION_KEY_FPR"),
      // this is only needed for development, so we just read the environment
      gnupghome: readEnvironment("GNUPGHOME", ""),
      // TODO: implement SD_PROXY_VM_NAME
      is_qubes: isQubes,
    };
  }
}

/**
 * Read a configuration value, either from QubesDB or the environment
 */
function read(isQubes: boolean, key: string, defaultValue?: string): string {
  let value;
  if (isQubes) {
    value = readQubesDB(key, defaultValue);
  } else {
    value = readEnvironment(key, defaultValue);
  }
  if (value === undefined) {
    throw new Error(`Missing configuration value: ${key}`);
  }
  return value;
}

function readQubesDB(key: string, defaultValue?: string): string | undefined {
  const fullkey = `/vm-config/${key}`;

  const result = spawnSync("qubesdb-read", [fullkey], {
    encoding: "utf8",
    timeout: 1000,
  });

  // Handle process spawn error
  if (result.error) {
    throw result.error;
  }

  // Handle timeout (signal will be 'SIGTERM')
  if (result.signal) {
    throw new Error(`Process terminated with signal ${result.signal}`);
  }

  // Non-existent key
  if (result.status === 2) {
    if (defaultValue !== undefined) {
      return defaultValue;
    }
    return undefined;
  }

  // Other non-zero exit codes
  if (result.status !== 0) {
    throw new Error(
      `Process exited with non-zero code ${result.status}: ${result.stderr}`,
    );
  }

  return result.stdout.trim();
}

function detectQubes(): boolean {
  return Object.keys(process.env).some((key) => key.startsWith("QUBES_"));
}

function readEnvironment(
  key: string,
  defaultValue?: string,
): string | undefined {
  return import.meta.env[key] || defaultValue;
}
