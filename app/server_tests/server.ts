/**
 * Manages isolated SecureDrop server instances using Docker or Podman.
 * Each test file can spin up its own server with fresh fixture data.
 *
 * Since tests run sequentially (singleFork: true in vitest config),
 * we don't need complex port allocation - each test file tears down
 * its server before the next one starts.
 */

import { execSync, spawn, ChildProcess } from "child_process";
import { resolve, dirname } from "path";
import { existsSync } from "fs";
import { fileURLToPath } from "url";

// Get __dirname equivalent for ESM
const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

const JOURNALIST_INTERFACE_PORT = 8081;
// Container name includes "-0" suffix because OFFSET_PORTS=false means port_offset=0
const CONTAINER_NAME = "securedrop-dev-0";

// Determine whether to use podman or docker
const CONTAINER_BIN = process.env.USE_PODMAN ? "podman" : "docker";

export class ServerInstance {
  private containerProcess: ChildProcess | null = null;
  private _origin: string = "";

  /**
   * Get the origin URL for the journalist interface.
   * Only valid after start() has been called.
   */
  get origin(): string {
    if (!this._origin) {
      throw new Error("Server not started. Call start() first.");
    }
    return this._origin;
  }

  /**
   * Start a new isolated SecureDrop server instance.
   * The server is initialized with the test fixture data.
   */
  async start(): Promise<void> {
    const securedropPath = this.getSecuredropPath();
    const fixtureDataPath = resolve(__dirname, "data");

    console.log(`Starting SecureDrop server container: ${CONTAINER_NAME}`);
    console.log(`SecureDrop path: ${securedropPath}`);
    console.log(`Fixture data path: ${fixtureDataPath}`);

    // Ensure no stale container with this name exists
    try {
      execSync(`${CONTAINER_BIN} rm -f ${CONTAINER_NAME}`, {
        stdio: "ignore",
        timeout: 10000,
      });
    } catch {
      // Container might not exist
    }

    // Start the server by running dev-shell directly (not via make dev)
    // This allows us to control DOCKER_BUILD_VERBOSE which must be false
    // to avoid /dev/stdout redirection issues in spawned processes
    const devShell = resolve(securedropPath, "securedrop/bin/dev-shell");
    const runScript = resolve(securedropPath, "securedrop/bin/run");

    this.containerProcess = spawn(devShell, [runScript], {
      env: {
        ...process.env,
        USE_FIXED_DATA: resolve(fixtureDataPath, "data.yaml"),
        OFFSET_PORTS: "false",
        SLIM_BUILD: "1",
        // Must be false to avoid /dev/stdout redirection issues
        DOCKER_BUILD_VERBOSE: "false",
      },
      cwd: securedropPath,
      stdio: "inherit",
      detached: true,
    });

    this.containerProcess.on("error", (err) => {
      console.error(`Server process error: ${err.message}`);
    });

    this._origin = `http://127.0.0.1:${JOURNALIST_INTERFACE_PORT}`;

    // Wait for the server to be ready
    await this.waitForReady();

    console.log(`SecureDrop server running at ${this._origin}`);
  }

  /**
   * Wait for the server to be ready by polling the API.
   * Timeout is 2 minutes to allow for container startup.
   */
  private async waitForReady(timeout = 120000): Promise<void> {
    const start = Date.now();
    const pollInterval = 2000;

    console.log(`Waiting for server to be ready at ${this._origin}...`);

    while (Date.now() - start < timeout) {
      try {
        const response = await fetch(`${this._origin}/api/v2/`, {
          method: "GET",
          signal: AbortSignal.timeout(5000),
        });
        // The API returns 401/403 without proper auth, which means it's up
        if (response.status === 401 || response.status === 403 || response.ok) {
          console.log(`Server is ready (status: ${response.status})`);
          return;
        }
      } catch {
        // Server not ready yet, continue polling
      }
      await new Promise((r) => setTimeout(r, pollInterval));
    }

    throw new Error(`Server failed to start within ${timeout}ms`);
  }

  /**
   * Stop and remove the server container.
   */
  async stop(): Promise<void> {
    console.log(`Stopping SecureDrop server container: ${CONTAINER_NAME}`);

    // Stop the container
    try {
      execSync(`${CONTAINER_BIN} stop ${CONTAINER_NAME}`, {
        stdio: "ignore",
        timeout: 30000,
      });
    } catch {
      // Container might not exist or already stopped
    }

    // Remove the container
    try {
      execSync(`${CONTAINER_BIN} rm -f ${CONTAINER_NAME}`, {
        stdio: "ignore",
        timeout: 10000,
      });
    } catch {
      // Container might not exist
    }

    // Kill the process if still running
    if (this.containerProcess?.pid) {
      try {
        // Kill the process group
        process.kill(-this.containerProcess.pid, "SIGTERM");
      } catch {
        // Process might already be dead
      }
      this.containerProcess = null;
    }

    this._origin = "";

    console.log("Server stopped.");
  }

  /**
   * Get the path to the SecureDrop server source.
   * Uses SERVER_PATH environment variable if set, otherwise defaults to ../../../securedrop
   */
  private getSecuredropPath(): string {
    const defaultPath = resolve(__dirname, "../../../securedrop");
    const serverPath = process.env.SERVER_PATH || defaultPath;
    const resolvedPath = resolve(serverPath);

    if (existsSync(resolve(resolvedPath, "securedrop", "manage.py"))) {
      return resolvedPath;
    }

    throw new Error(
      `Could not find SecureDrop server source at: ${resolvedPath}`,
    );
  }
}

// Singleton for managing the global server instance per test file
let globalServer: ServerInstance | null = null;

/**
 * Get or create the global server instance for the current test file.
 * The server is started lazily on first access.
 */
export async function getServerInstance(): Promise<ServerInstance> {
  if (!globalServer) {
    globalServer = new ServerInstance();
    await globalServer.start();
  }
  return globalServer;
}

/**
 * Stop the global server instance.
 * Should be called in afterAll() of each test file.
 */
export async function stopServerInstance(): Promise<void> {
  if (globalServer) {
    await globalServer.stop();
    globalServer = null;
  }
}
