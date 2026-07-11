import "source-map-support/register";
import {
  app,
  BrowserWindow,
  dialog,
  ipcMain,
  session,
  clipboard,
} from "electron";
import { join, delimiter } from "path";
import { randomBytes } from "crypto";

import { optimizer, is } from "@electron-toolkit/utils";
import { Worker } from "worker_threads";
import fs from "fs";
import os from "os";
import { spawn, spawnSync } from "child_process";

import { Datastore } from "./datastore";
import { Crypto, CryptoConfig } from "./crypto";
import { proxyJSONRequest } from "./proxy";
import {
  type Source,
  type SourceWithItems,
  type SourceItemCounts,
  type Journalist,
  type AuthedRequest,
  type SyncRequest,
  type LoginCredentials,
  type LoginResult,
  type Item,
  type DeviceStatus,
  type SearchResult,
  type FirstRunStatus,
  FetchStatus,
  PendingEventType,
  SyncStatus,
  PendingEventData,
  type ms,
} from "../types";
import {
  TokenResponseSchema,
  API_MINOR_VERSION,
  EventUpperBoundSchema,
  validatePendingEventData,
} from "../schemas";
import { syncMetadata, shouldSkipSync } from "./sync";
import workerPath from "./fetch/worker?modulePath";
import { Lock, LockTimeoutError } from "./sync/lock";
import { sleep } from "./timeouts";
import { Config } from "./config";
import { setUmask } from "./umask";
import { Exporter, Printer } from "./export";
import { Storage } from "./storage";
import { writeTranscript } from "./transcriber";
import { initLogging } from "./log";

// Set umask so any files written are owner-only read/write (600).
// This must be done before we create any files or spawn any worker threads.
setUmask();

initLogging();

// Handle --version flag early, before any other initialization
if (process.argv.includes("--version")) {
  console.log(`SecureDrop Inbox v${app.getVersion()}`);
  process.exit(0);
}

// Enforce single instance - quit if another instance is already running.
// This must be checked early before allocating resources.
const gotTheLock = app.requestSingleInstanceLock();
if (!gotTheLock) {
  app
    .whenReady()
    .then(() => {
      dialog
        .showMessageBox({
          type: "info",
          title: "SecureDrop Inbox",
          // TODO: ideally this would be localized
          message: "The SecureDrop Inbox is already running.",
          buttons: ["OK"],
        })
        .then(() => {
          app.quit();
        });
    })
    .catch((error) => {
      console.error(
        "Failed to show 'already running' dialog during app startup:",
        error,
      );
      process.exit(1);
    });
} else {
  // For mac-demo mode: set up GPG keyring at runtime
  // Add common GPG installation directories to PATH for macOS
  if (import.meta.env.MODE === "mac-demo") {
    const gpgPaths = [
      "/opt/homebrew/bin", // Homebrew on Apple Silicon
      "/usr/local/bin", // Homebrew on Intel Mac
      "/usr/local/MacGPG2/bin", // GPG Suite
    ];
    process.env.PATH = [...gpgPaths, process.env.PATH].join(delimiter);

    const gpgHome = fs.mkdtempSync(
      join(fs.realpathSync(os.tmpdir()), "sd-app-gpg-"),
    );
    const keyPath = join(
      process.resourcesPath,
      "keys",
      "securedrop-test-key.asc",
    );

    const result = spawnSync("gpg", [
      "--homedir",
      gpgHome,
      "--import",
      keyPath,
    ]);
    if (result.error) {
      throw result.error;
    } else if (result.status !== 0) {
      throw new Error(
        `gpg import failed with code ${result.status}: ${result.stderr}`,
      );
    }

    process.env.GNUPGHOME = gpgHome;
    console.log(`Mac demo mode: GPG keyring initialized at ${gpgHome}`);
  }

  // Parse command line arguments
  const args = process.argv.slice(2);
  const noQubes = args.includes("--no-qubes");
  const noFirstRun = args.includes("--no-first-run");
  const shouldAutoLogin = args.includes("--login");

  // Load config
  const config = Config.load(noQubes);

  function initializeMainDependencies(): {
    db: Datastore;
    cryptoConfig: CryptoConfig;
  } {
    try {
      // Create crypto config + initialize
      const configForCrypto: CryptoConfig = {
        submissionKeyFingerprint: config.sd_submission_key_fpr,
        isQubes: config.is_qubes,
        gpgHomedir: config.gnupghome || undefined,
        qubesGpgDomain: config.qubes_gpg_domain,
      };

      const crypto = Crypto.initialize(configForCrypto);
      const storage = new Storage();
      const appDb = new Datastore(crypto, storage);

      return {
        db: appDb,
        cryptoConfig: configForCrypto,
      };
    } catch (error) {
      console.error("Failed to initialize SecureDrop Inbox:", error);
      process.exit(1);
    }
  }

  const { db, cryptoConfig } = initializeMainDependencies();
  const startupCleanup = db.cleanupInvalidLifecycleData();

  // Generate a CSP nonce for this session (used by Ant Design)
  const cspNonce = randomBytes(32).toString("base64");

  // Get Vite nonce from build-time generated value (injected via define in vite config)
  const viteNonce =
    is.dev && process.env["NODE_ENV"] != "production" ? __VITE_NONCE__ : "";

  // Set to true by the `before-quit` event so the close intercept allows
  // programmatic quit (IPC quitApp, OS signals, etc.)
  let isQuitting = false;

  function createWindow(): BrowserWindow {
    const mainWindow = new BrowserWindow({
      width: is.dev && process.env["NODE_ENV"] != "production" ? 1500 : 1200,
      height: 700,
      minWidth: 1200,
      minHeight: 700,
      title: "SecureDrop Inbox",
      icon: join(__dirname, "../../resources/images/logo.png"),
      show: false,
      autoHideMenuBar: true,
      webPreferences: {
        preload: join(__dirname, "../preload/index.js"),
        sandbox: true,
        spellcheck: false,
      },
    });

    mainWindow.on("ready-to-show", () => {
      mainWindow.show();
      // Default open DevTools in development
      // We're checking for both is.dev and NODE_ENV isn't production so that `pnpm start`, which previews
      // the production build, doesn't open DevTools
      if (is.dev && process.env["NODE_ENV"] != "production") {
        mainWindow.webContents.openDevTools();
      }
    });

    // HMR for renderer base on electron-vite cli.
    // Load the remote URL for development or the local html file for production.
    if (is.dev && process.env["ELECTRON_RENDERER_URL"]) {
      mainWindow.loadURL(process.env["ELECTRON_RENDERER_URL"]);
    } else {
      mainWindow.loadFile(join(__dirname, "../renderer/index.html"));
    }

    // Intercept the window close button (X) to show the quit confirmation
    // modal in the renderer instead of quitting immediately.
    // When app.quit() is called (e.g. from the renderer's quitApp IPC),
    // the `before-quit` event sets `isQuitting` so the close handler lets
    // it through.
    mainWindow.on("close", (e) => {
      if (!isQuitting && !mainWindow.isDestroyed()) {
        e.preventDefault();
        mainWindow.webContents.send("quit-requested");
      }
    });

    return mainWindow;
  }

  function spawnFetchWorker(mainWindow: BrowserWindow): Worker {
    const worker = new Worker(workerPath, {
      workerData: { cryptoConfig },
    });

    worker.on("message", (result) => {
      console.debug("Message from worker: ", result);
      if (!result) {
        return;
      }
      // Check if worker update is Source or Item
      if (result && "messagePreview" in result) {
        mainWindow.webContents.send("source-update", result);
      } else {
        mainWindow.webContents.send("item-update", result);
      }
    });

    worker.on("error", (err) => {
      console.log("Error from worker: ", err);
    });

    worker.on("exit", (err) => {
      console.log("Worker exited with code ", err);
    });

    worker.on("messageerror", (err) => {
      console.log("Message error from worker: ", err);
    });

    return worker;
  }

  let fetchWorker: Worker | null = null;
  let authToken: string | null = null;
  let syncLoopTimer: NodeJS.Timeout | null = null;
  let lastHintedRecords: number | undefined;

  function wakeFetchWorkerIfNeeded(): void {
    if (!fetchWorker) {
      return;
    }

    fetchWorker.postMessage({ type: "authedRequest", request: { authToken } });
  }

  // This method will be called when Electron has finished
  // initialization and is ready to create browser windows.
  // Some APIs can only be used after this event occurs.
  app
    .whenReady()
    .then(() => startupCleanup)
    .then(() => {
      // Set strict Content Security Policy via HTTP header with nonce
      session.defaultSession.webRequest.onHeadersReceived(
        (details, callback) => {
          // Don't set a CSP for devtools when we're in dev mode
          if (
            is.dev &&
            process.env["NODE_ENV"] != "production" &&
            (details.url.startsWith("devtools://") ||
              details.url.startsWith("chrome-extension://"))
          ) {
            callback({ responseHeaders: details.responseHeaders });
            return;
          }
          let scriptSrc = "script-src 'self'";
          let styleSrc = `style-src 'self' 'nonce-${cspNonce}'`;
          let connectSrc = "";
          if (is.dev && process.env["NODE_ENV"] != "production") {
            // Inject vite's nonce for auto-reload
            scriptSrc += ` 'nonce-${viteNonce}'`;
            styleSrc += ` 'nonce-${viteNonce}'`;
            connectSrc = "connect-src 'self';";
          }

          callback({
            responseHeaders: {
              ...details.responseHeaders,
              "Content-Security-Policy": [
                "default-src 'none'; " +
                  scriptSrc +
                  "; " +
                  styleSrc +
                  "; " +
                  "img-src 'self'; " +
                  "font-src 'self'; " +
                  connectSrc,
              ],
            },
          });
        },
      );
      // Load developer tools
      if (is.dev && !__IS_PRODUCTION__) {
        import("electron-devtools-installer")
          .then(({ installExtension, REACT_DEVELOPER_TOOLS, REDUX_DEVTOOLS }) =>
            installExtension([REACT_DEVELOPER_TOOLS, REDUX_DEVTOOLS]),
          )
          .then(([react, redux]) =>
            console.log(`Added extensions: ${react.name}, ${redux.name}`),
          )
          .catch((err) =>
            console.log("An error occurred during extension setup: ", err),
          );
      }

      const syncLock = new Lock();

      // Default open or close DevTools by F12 in development
      // and ignore CommandOrControl + R in production.
      // see https://github.com/alex8088/electron-toolkit/tree/master/packages/utils
      app.on("browser-window-created", (_, window) => {
        optimizer.watchWindowShortcuts(window);
      });

      // Initialize exporter
      const exporter = new Exporter();
      const printer = new Printer();

      ipcMain.handle("quitApp", () => {
        app.quit();
      });

      ipcMain.handle("getAppVersion", async (_event): Promise<string> => {
        return app.getVersion();
      });

      ipcMain.handle(
        "login",
        async (_event, credentials: LoginCredentials): Promise<LoginResult> => {
          // Clear authToken on new login attempt
          authToken = null;
          try {
            const result = await proxyJSONRequest(
              {
                method: "POST",
                path_query: "/api/v1/token",
                stream: false,
                body: JSON.stringify({
                  username: credentials.username,
                  passphrase: credentials.passphrase,
                  one_time_code: credentials.oneTimeCode,
                }),
                headers: { Prefer: `securedrop=${API_MINOR_VERSION}` },
              },
              undefined,
              30_000 as ms,
            );
            if (result.status === 403) {
              return { success: false, errorType: "credentials" };
            }
            // TODO: use a dedicated error message here that exposes the code
            if (result.status !== 200 || !result.data) {
              console.error(
                `Authentication failed with HTTP status ${result.status}`,
                result.data,
              );
              return { success: false, errorType: "generic" };
            }

            const resp = TokenResponseSchema.safeParse(result.data);
            if (!resp.success) {
              return { success: false, errorType: "generic" };
            }
            authToken = resp.data.token;
            lastHintedRecords = resp.data.hints.sources + resp.data.hints.items;

            // Initiate sync loop
            if (import.meta.env.MODE != "test") {
              void runSyncLoop({ hintedRecords: lastHintedRecords });
            }

            return {
              success: true,
              expiration: resp.data.expiration,
              journalistUUID: resp.data.journalist_uuid,
              journalistFirstName: resp.data.journalist_first_name,
              journalistLastName: resp.data.journalist_last_name,
              lastHintedVersion: resp.data.hints.version,
              lastHintedSources: resp.data.hints.sources,
              lastHintedItems: resp.data.hints.items,
            };
          } catch {
            return { success: false, errorType: "network" };
          }
        },
      );

      ipcMain.handle(
        "getSources",
        async (_event): Promise<Record<string, Source>> => {
          return Object.fromEntries(db.getSources());
        },
      );

      ipcMain.handle(
        "getSourceWithItems",
        async (
          _event,
          sourceUuid: string,
          options?: {
            limit?: number;
            beforeInteractionCount?: number;
            journalistUuid?: string;
          },
        ): Promise<SourceWithItems> => {
          const sourceWithItems = db.getSourceWithItems(sourceUuid, options);
          return sourceWithItems;
        },
      );

      ipcMain.handle(
        "getSourceItemCounts",
        async (_event, sourceUuids: string[]): Promise<SourceItemCounts> => {
          return db.getSourceItemCounts(sourceUuids);
        },
      );

      ipcMain.handle(
        "getItem",
        async (_event, itemUuid: string): Promise<Item | null> => {
          return db.getItem(itemUuid);
        },
      );

      ipcMain.handle(
        "getJournalists",
        async (_event): Promise<Journalist[]> => {
          const journalists = db.getJournalists();
          return journalists;
        },
      );

      ipcMain.handle(
        "search",
        async (_event, query: string): Promise<SearchResult[]> => {
          return db.search(query);
        },
      );

      ipcMain.handle(
        "updateFetchStatus",
        async (_event, itemUuid: string, fetchStatus: number) => {
          // If the user is pausing or cancelling, abort any in-progress download
          // before updating the DB so the worker doesn't overwrite the new status
          if (
            fetchStatus === FetchStatus.Paused ||
            fetchStatus === FetchStatus.Cancelled
          ) {
            fetchWorker?.postMessage({ type: "cancel", itemId: itemUuid });
          }
          db.updateFetchStatus(itemUuid, fetchStatus);
          wakeFetchWorkerIfNeeded();
        },
      );

      ipcMain.handle(
        "syncMetadata",
        async (_event, request: SyncRequest): Promise<SyncStatus> => {
          return runSyncLoop(request);
        },
      );

      ipcMain.handle("getSystemLanguage", async (_event): Promise<string> => {
        const systemLanguage = process.env.LANG || app.getLocale() || "en";
        return systemLanguage;
      });

      function abortSourceFetch(
        sourceUuid: string,
        type: PendingEventType,
      ): void {
        const deletesSourceData =
          type === PendingEventType.SourceDeleted ||
          type === PendingEventType.SourceConversationTruncated;
        if (deletesSourceData && fetchWorker) {
          fetchWorker.postMessage({ type: "abortSourceFetch", sourceUuid });
        }
      }

      ipcMain.handle(
        "addPendingSourceEvent",
        async (
          _event,
          sourceUuid: string,
          type: PendingEventType,
          data?: PendingEventData,
        ): Promise<string | null> => {
          validatePendingEventData(type, data);
          const eventId = db.addPendingSourceEvent(sourceUuid, type, data);
          abortSourceFetch(sourceUuid, type);
          await db.runFilesystemCleanupJobs();
          return eventId;
        },
      );

      ipcMain.handle(
        "addPendingSourceEventBatch",
        async (
          _event,
          events: Array<{
            sourceUuid: string;
            type: PendingEventType;
            data?: PendingEventData;
          }>,
        ): Promise<(string | null)[]> => {
          for (const { type, data } of events) {
            validatePendingEventData(type, data);
          }
          const eventIds = db.addPendingSourceEventBatch(events);
          for (const { sourceUuid, type } of events) {
            abortSourceFetch(sourceUuid, type);
          }
          await db.runFilesystemCleanupJobs();
          return eventIds;
        },
      );

      ipcMain.handle(
        "addPendingReplySentEvent",
        async (
          _event,
          text: string,
          sourceUuid: string,
          interactionCount: number,
        ): Promise<string> => {
          return db.addPendingReplySentEvent(
            text,
            sourceUuid,
            interactionCount,
          );
        },
      );

      ipcMain.handle(
        "addPendingItemEvent",
        async (
          _event,
          itemUuid: string,
          type: PendingEventType,
        ): Promise<string | null> => {
          const eventId = db.addPendingItemEvent(itemUuid, type);
          await db.runFilesystemCleanupJobs();
          return eventId;
        },
      );

      ipcMain.handle(
        "addPendingSourceConversationSeen",
        async (
          _event,
          sourceUuid: string,
          upperBound: number,
        ): Promise<string | null> => {
          return db.addPendingSourceConversationSeen(
            sourceUuid,
            EventUpperBoundSchema.parse(upperBound),
          );
        },
      );

      ipcMain.handle("shouldAutoLogin", async (_event): Promise<boolean> => {
        // Only honor auto-login in development mode
        return is.dev && shouldAutoLogin;
      });

      ipcMain.handle(
        "getWhistleflowEnabled",
        async (_event): Promise<boolean> => {
          return config.whistleflow;
        },
      );

      ipcMain.handle("getCSPNonce", async (_event): Promise<string> => {
        return cspNonce;
      });

      ipcMain.handle("clearClipboard", async (_event): Promise<void> => {
        clipboard.clear();
        clipboard.clear("selection");
        return;
      });

      ipcMain.handle(
        "openFile",
        async (_event, itemUuid: string): Promise<void> => {
          const item = db.getItem(itemUuid);
          if (!item || !item.filename) {
            throw new Error(`Item ${itemUuid} has not been downloaded yet`);
          }

          const filePath = item.filename;

          // Double-check it exists before we open it
          if (!fs.existsSync(filePath)) {
            throw new Error(`File not found: ${filePath}`);
          }

          // Unconditionally open in the sd-viewer dispVM
          const command = "qvm-open-in-vm";
          // spawn() does not use a shell so these don't need escaping
          const args = ["--view-only", "@dispvm:sd-viewer", filePath];

          const process = spawn(command, args);
          // Log errors but don't wait for the process to finish
          process.on("error", (error) => {
            console.error(`Failed to launch qvm-open-in-vm: ${error.message}`);
          });

          // Return immediately without waiting for the process to finish
        },
      );

      // Print + export IPCs
      ipcMain.handle(
        "initiateExport",
        async (_event): Promise<DeviceStatus> => {
          return exporter.initiateExport();
        },
      );

      ipcMain.handle(
        "exportTranscript",
        async (
          _event,
          sourceUuid: string,
          passphrase: string,
          whistleflow?: boolean,
        ): Promise<DeviceStatus> => {
          try {
            const filePath: string = await writeTranscript(sourceUuid, db);

            if (!fs.existsSync(filePath)) {
              throw new Error(`Transcript file not found: ${filePath}`);
            }
            const sourceWithItems = db.getSourceWithItems(sourceUuid);
            const sourceName = sourceWithItems.data.journalist_designation;
            return await exporter.export(
              [filePath],
              passphrase,
              sourceName,
              whistleflow,
            );
          } catch (error) {
            console.error(
              `Failed to export transcript for source: ${sourceUuid}:`,
              error,
            );
            throw error;
          }
        },
      );

      ipcMain.handle(
        "export",
        async (
          _event,
          itemUuids: string[],
          passphrase: string,
          whistleflow?: boolean,
        ): Promise<DeviceStatus> => {
          const filenames: string[] = [];
          let sourceName: string | undefined;
          for (const itemUuid of itemUuids) {
            const item = db.getItem(itemUuid);
            if (
              !item ||
              !item.filename ||
              item.fetch_status !== FetchStatus.Complete
            ) {
              throw new Error(`Item ${itemUuid} has not been downloaded yet`);
            }
            if (!fs.existsSync(item.filename)) {
              throw new Error(`File not found: ${item.filename}`);
            }
            filenames.push(item.filename);
            if (!sourceName) {
              const source = db.getSourceWithItems(item.data.source);
              sourceName = source.data.journalist_designation;
            }
          }
          return await exporter.export(
            filenames,
            passphrase,
            sourceName,
            whistleflow,
          );
        },
      );

      ipcMain.handle(
        "exportSource",
        async (
          _event,
          sourceUuid: string,
          passphrase: string,
          whistleflow?: boolean,
        ): Promise<DeviceStatus> => {
          try {
            const transcriptPath: string = await writeTranscript(
              sourceUuid,
              db,
            );

            if (!fs.existsSync(transcriptPath)) {
              throw new Error(`Transcript file not found: ${transcriptPath}`);
            }

            const sourceWithItems = db.getSourceWithItems(sourceUuid);
            const filenames: string[] = [transcriptPath];
            for (const item of sourceWithItems.items) {
              if (
                item.data.kind === "file" &&
                item.fetch_status === FetchStatus.Complete &&
                item.filename &&
                fs.existsSync(item.filename)
              ) {
                filenames.push(item.filename);
              }
            }
            const sourceName = sourceWithItems.data.journalist_designation;
            return await exporter.export(
              filenames,
              passphrase,
              sourceName,
              whistleflow,
            );
          } catch (error) {
            console.error(`Failed to export source: ${sourceUuid}:`, error);
            throw error;
          }
        },
      );

      ipcMain.handle("initiatePrint", async (_event): Promise<DeviceStatus> => {
        return printer.initiatePrint();
      });

      ipcMain.handle(
        "printTranscript",
        async (_event, sourceUuid: string): Promise<DeviceStatus> => {
          try {
            const filePath: string = await writeTranscript(sourceUuid, db);

            if (!fs.existsSync(filePath)) {
              throw new Error(`Transcript file not found: ${filePath}`);
            }
            return printer.print([filePath]);
          } catch (error) {
            console.error(
              `Failed to print transcript for source: ${sourceUuid}:`,
              error,
            );
            throw error;
          }
        },
      );

      ipcMain.handle(
        "print",
        async (_event, itemUuid: string): Promise<DeviceStatus> => {
          const item = db.getItem(itemUuid);
          if (
            !item ||
            !item.filename ||
            item.fetch_status !== FetchStatus.Complete
          ) {
            throw new Error(`Item ${itemUuid} has not been downloaded yet`);
          }
          if (!fs.existsSync(item.filename)) {
            throw new Error(`File not found: ${item.filename}`);
          }
          return printer.print([item.filename]);
        },
      );

      ipcMain.handle("cancelExport", async (_event): Promise<void> => {
        exporter.cancelExport();
      });

      ipcMain.handle("cancelPrint", async (_event): Promise<void> => {
        printer.cancelPrint();
      });

      ipcMain.handle(
        "getFirstRunStatus",
        async (_event): Promise<FirstRunStatus> => {
          if (noFirstRun) {
            return null;
          }
          return db.getFirstRunStatus();
        },
      );

      const mainWindow = createWindow();

      fetchWorker = spawnFetchWorker(mainWindow);

      function scheduleNextSync(): void {
        if (syncLoopTimer) {
          clearTimeout(syncLoopTimer);
        }
        // Short-circuit loops on test
        if (import.meta.env.MODE === "test") {
          return;
        }

        syncLoopTimer = setTimeout(() => {
          if (authToken) {
            void runSyncLoop({ hintedRecords: lastHintedRecords });
          }
        }, 1000 * 60);
      }

      // Checks if sync is necessary, and then continually sync with the
      // server until all pending events are flushed. Schedules the next sync
      // after sync interval on completion.
      async function runSyncLoop(request: SyncRequest): Promise<SyncStatus> {
        try {
          if (!authToken) {
            return SyncStatus.FORBIDDEN;
          }
          if (shouldSkipSync(db, request.hintedVersion)) {
            console.log(`Already at ${request.hintedVersion}; skipping sync`);
            wakeFetchWorkerIfNeeded();
            return SyncStatus.NOT_MODIFIED;
          }

          // Clear timer to unschedule syncs until this loop is complete
          if (syncLoopTimer) {
            clearTimeout(syncLoopTimer);
          }

          // Keep syncing while there are still pending events to flush
          const authedRequest: AuthedRequest = { authToken, ...request };
          let syncStatus = SyncStatus.NOT_MODIFIED;
          do {
            syncStatus = await syncWithLock(syncLock, db, authedRequest);
            // Update renderer on each sync cycle completion
            if (!mainWindow.isDestroyed()) {
              mainWindow.webContents.send("sync-complete", syncStatus);
            }
            wakeFetchWorkerIfNeeded();
          } while (
            syncStatus === SyncStatus.UPDATED &&
            db.getPendingEvents().length > 0
          );
          // If we receive an auth error from sync, reset the auth token
          if (syncStatus === SyncStatus.FORBIDDEN) {
            authToken = null;
          }
          return syncStatus;
        } finally {
          scheduleNextSync();
        }
      }
    })
    .catch((error) => {
      console.error("Unhandled error during app startup:", error);
      app.exit(1);
    });

  app.on("window-all-closed", () => {
    app.quit();
  });

  app.on("before-quit", () => {
    isQuitting = true;
    db.close();
    if (fetchWorker) {
      fetchWorker.postMessage({ type: "exit" });
    }
  });
}

// syncWithLock attempts to acquire the sync lock and then perform
// metadata sync with the server. Retries up to MAX_SYNC_RETRIES times
// with exponential backoff and decreased batch sizes.
async function syncWithLock(
  syncLock: Lock,
  db: Datastore,
  request: AuthedRequest,
): Promise<SyncStatus> {
  const MAX_SYNC_RETRIES = 3;

  let retryCount = 0;
  while (true) {
    try {
      return await syncLock.run(async () => {
        console.log("[sync] Acquired lock");
        return await syncMetadata(
          db,
          request.authToken,
          request.hintedRecords,
          retryCount,
        );
      }, 1000);
    } catch (error) {
      if (error instanceof LockTimeoutError) {
        console.log("[sync] Failed to acquire lock");
        return SyncStatus.TIMEOUT;
      }
      if (retryCount >= MAX_SYNC_RETRIES) {
        console.log("[sync] Exceeded max retries", { error });
        throw error;
      }
      retryCount++;
      const backoffMs = (1000 * 2 ** retryCount) as ms;
      console.log(
        `[sync] Sync failed, sleeping for ${backoffMs}ms before retrying...`,
        { error },
      );
      await sleep(backoffMs);
    }
  }
}
