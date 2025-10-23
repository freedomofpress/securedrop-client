import child_process from "node:child_process";

/**
 * Config loads configuration at runtime from QubesDB (if available),
 * falling back to the environment in non-Qubes mode
 */
export class Config {
  // Configuration variables
  journalist_public_key!: string;
  is_qubes!: boolean;

  public static load(noQubes: boolean): Config {
    const isQubes = noQubes ? !noQubes : detectQubes();
    console.log("Loading with isQubes: ", isQubes);
    return {
      journalist_public_key: mustReadVar("SD_SUBMISSION_PUBKEY", isQubes),
      is_qubes: isQubes,
    };
  }
}

function detectQubes(): boolean {
  return Object.keys(process.env).some((key) => key.startsWith("QUBES_"));
}

// Reads a required variable, throwing an error if undefined
function mustReadVar(key: string, isQubes: boolean): string {
  const val = readVar(key, isQubes);
  if (typeof val === "undefined") {
    throw new Error(
      `unable to read config value for required variable ${key} using qubes ${isQubes}`,
    );
  }
  return val;
}

function readVar(key: string, isQubes: boolean): string | undefined {
  if (isQubes) {
    return readQubesDB(key);
  }
  return readEnvironment(key);
}

function readQubesDB(key: string): string | undefined {
  try {
    const value = child_process
      .execSync(`qubesdb-get /vm-config/${key}`, {
        encoding: "utf8",
      })
      .trim();
    console.log("Value: ", value);
    return value || undefined;
  } catch (e) {
    console.log("ERror: ", e);
    return undefined;
  }
}

function readEnvironment(key: string): string | undefined {
  return import.meta.env[key];
}
