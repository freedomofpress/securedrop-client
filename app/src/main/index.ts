import "source-map-support/register";
import {
  app,
  BrowserWindow,
  dialog,
  ipcMain,
  session,
  clipboard,
  Menu,
} from "electron";
import { join, dirname, delimiter } from "path";
import { randomBytes } from "crypto";

import { optimizer, is } from "@electron-toolkit/utils";
import {
  installExtension,
  REDUX_DEVTOOLS,
  REACT_DEVELOPER_TOOLS,
} from "electron-devtools-installer";
import { Worker } from "worker_threads";
import fs from "fs";
import os from "os";
import { spawn, spawnSync } from "child_process";

import { DB } from "./database";
import { Crypto, CryptoConfig } from "./crypto";
import { proxyJSONRequest } from "./proxy";
import {
  type ProxyRequest,
  type ProxyResponse,
  type Source,
  type SourceWithItems,
  type Journalist,
  type AuthedRequest,
  type Item,
  type PendingEventType,
  type DeviceStatus,
  FetchStatus,
  SyncStatus,
} from "../types";
import { syncMetadata, shouldSkipSync } from "./sync";
import workerPath from "./fetch/worker?modulePath";
import { Lock, LockTimeoutError } from "./sync/lock";
import { Config } from "./config";
import { setUmask } from "./umask";
import { Exporter, Printer } from "./export";
import { Storage } from "./storage";
import { writeTranscript } from "./transcriber";

// Set umask so any files written are owner-only read/write (600).
// This must be done before we create any files or spawn any worker threads.
setUmask();

// Handle --version flag early, before any other initialization
if (process.argv.includes("--version")) {
  console.log(`SecureDrop App v${app.getVersion()}`);
  process.exit(0);
}

// Enforce single instance - quit if another instance is already running.
// This must be checked early before allocating resources.
const gotTheLock = app.requestSingleInstanceLock();
if (!gotTheLock) {
  app.whenReady().then(() => {
    dialog
      .showMessageBox({
        type: "info",
        title: "SecureDrop App",
        // TODO: ideally this would be localized
        message: "The SecureDrop App is already running.",
        buttons: ["OK"],
      })
      .then(() => {
        app.quit();
      });
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
  const shouldAutoLogin = args.includes("--login");

  const config = Config.load(noQubes);

  // Create crypto config + initialize
  const cryptoConfig: CryptoConfig = {
    submissionKeyFingerprint: config.sd_submission_key_fpr,
    isQubes: config.is_qubes,
    gpgHomedir: config.gnupghome || undefined,
    qubesGpgDomain: config.qubes_gpg_domain,
  };

  const crypto = Crypto.initialize(cryptoConfig);

  const db = new DB(crypto);

  // Generate a CSP nonce for this session (used by Ant Design)
  const cspNonce = randomBytes(32).toString("base64");

  // Get Vite nonce from build-time generated value (injected via define in vite config)
  const viteNonce =
    is.dev && process.env["NODE_ENV"] != "production" ? __VITE_NONCE__ : "";

  function createWindow(): BrowserWindow {
    const mainWindow = new BrowserWindow({
      width: is.dev && process.env["NODE_ENV"] != "production" ? 1500 : 1200,
      height: 900,
      minWidth: 1200,
      minHeight: 900,
      title: "SecureDrop App",
      icon: join(__dirname, "../renderer/resources/icon.png"),
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

    return mainWindow;
  }

  function spawnFetchWorker(mainWindow: BrowserWindow): Worker {
    const worker = new Worker(workerPath, {
      workerData: { cryptoConfig },
    });

    worker.on("message", (result) => {
      console.debug("Message from worker: ", result);
      // Check if worker update is Source or Item
      if ("messagePreview" in result) {
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

  // This method will be called when Electron has finished
  // initialization and is ready to create browser windows.
  // Some APIs can only be used after this event occurs.
  app.whenReady().then(() => {
    // Set strict Content Security Policy via HTTP header with nonce
    session.defaultSession.webRequest.onHeadersReceived((details, callback) => {
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
    });
    // Load developer tools
    if (is.dev) {
      installExtension([REACT_DEVELOPER_TOOLS, REDUX_DEVTOOLS])
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

    // Set up application menu with keyboard shortcuts
    const template: Electron.MenuItemConstructorOptions[] = [
      {
        label: "Application",
        submenu: [
          {
            label: "Quit",
            accelerator: "CmdOrCtrl+Q",
            click: () => {
              app.quit();
            },
          },
        ],
      },
    ];
    const menu = Menu.buildFromTemplate(template);
    Menu.setApplicationMenu(menu);

    // Initialize exporter
    const exporter = new Exporter();
    const printer = new Printer();

    ipcMain.handle(
      "request",
      async (_event, request: ProxyRequest): Promise<ProxyResponse> => {
        const result = await proxyJSONRequest(request);
        return result;
      },
    );

    ipcMain.handle("getSources", async (_event): Promise<Source[]> => {
      const sources = db.getSources();
      return sources;
    });

    ipcMain.handle(
      "getSourceWithItems",
      async (_event, sourceUuid: string): Promise<SourceWithItems> => {
        const sourceWithItems = db.getSourceWithItems(sourceUuid);
        return sourceWithItems;
      },
    );

    ipcMain.handle(
      "getItem",
      async (_event, itemUuid: string): Promise<Item | null> => {
        return db.getItem(itemUuid);
      },
    );

    ipcMain.handle("getJournalists", async (_event): Promise<Journalist[]> => {
      const journalists = db.getJournalists();
      return journalists;
    });

    ipcMain.handle(
      "updateFetchStatus",
      async (
        _event,
        itemUuid: string,
        fetchStatus: number,
        authToken: string,
      ) => {
        // When resetting to Initial or DownloadInProgress, clean up partial download files
        if (
          fetchStatus === FetchStatus.Initial ||
          fetchStatus === FetchStatus.DownloadInProgress
        ) {
          const item = db.getItem(itemUuid);
          if (item && item.data.kind === "file") {
            const storage = new Storage();
            const downloadDir = storage.downloadFilePath(item.data, {
              id: itemUuid,
            });
            // Delete the entire download directory for this item
            const dirPath = dirname(downloadDir);
            try {
              fs.rmSync(dirPath, { recursive: true, force: true });
              console.debug(
                `Cleaned up partial download directory: ${dirPath}`,
              );
            } catch (err) {
              console.warn(
                `Failed to clean up partial download directory ${dirPath}:`,
                err,
              );
            }
          }
        }
        db.updateFetchStatus(itemUuid, fetchStatus);
        fetchWorker.postMessage({
          authToken: authToken,
        } as AuthedRequest);
      },
    );

    ipcMain.handle(
      "syncMetadata",
      async (_event, request: AuthedRequest): Promise<SyncStatus> => {
        if (shouldSkipSync(db, request.hintedVersion)) {
          console.debug(`Already at ${request.hintedVersion}; skipping sync`);
          return SyncStatus.NOT_MODIFIED;
        }

        let syncStatus: SyncStatus;
        try {
          syncStatus = await syncLock.run(async () => {
            return await syncMetadata(
              db,
              request.authToken,
              request.hintedRecords,
            );
          }, 1000);
        } catch (error) {
          // Check if this is a timeout error from the lock
          if (error instanceof LockTimeoutError) {
            return SyncStatus.TIMEOUT;
          }
          throw error;
        }

        if (syncStatus === SyncStatus.UPDATED) {
          fetchWorker.postMessage({
            authToken: request.authToken,
          } as AuthedRequest);
        }

        return syncStatus;
      },
    );

    ipcMain.handle("getSystemLanguage", async (_event): Promise<string> => {
      const systemLanguage = process.env.LANG || app.getLocale() || "en";
      return systemLanguage;
    });

    ipcMain.handle(
      "addPendingSourceEvent",
      async (
        _event,
        sourceUuid: string,
        type: PendingEventType,
      ): Promise<string> => {
        return db.addPendingSourceEvent(sourceUuid, type);
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
        return db.addPendingReplySentEvent(text, sourceUuid, interactionCount);
      },
    );

    ipcMain.handle(
      "addPendingItemEvent",
      async (
        _event,
        itemUuid: string,
        type: PendingEventType,
      ): Promise<string> => {
        return db.addPendingItemEvent(itemUuid, type);
      },
    );

    ipcMain.handle(
      "addPendingItemsSeenBatch",
      async (
        _event,
        sourceUuid: string,
        itemUuids: string[],
      ): Promise<bigint[]> => {
        return db.addPendingItemsSeenBatch(sourceUuid, itemUuids);
      },
    );

    ipcMain.handle("shouldAutoLogin", async (_event): Promise<boolean> => {
      // Only honor auto-login in development mode
      return is.dev && shouldAutoLogin;
    });

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
    ipcMain.handle("initiateExport", async (_event): Promise<DeviceStatus> => {
      return exporter.initiateExport();
    });

    ipcMain.handle(
      "exportTranscript",
      async (
        _event,
        sourceUuid: string,
        passphrase: string,
      ): Promise<DeviceStatus> => {
        try {
          const filePath: string = await writeTranscript(sourceUuid, db);

          if (!fs.existsSync(filePath)) {
            throw new Error(`Transcript file not found: ${filePath}`);
          }
          const sourceWithItems = db.getSourceWithItems(sourceUuid);
          const sourceName = sourceWithItems.data.journalist_designation;
          return await exporter.export([filePath], passphrase, sourceName);
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
        return await exporter.export(filenames, passphrase, sourceName);
      },
    );

    ipcMain.handle(
      "exportSource",
      async (
        _event,
        sourceUuid: string,
        passphrase: string,
      ): Promise<DeviceStatus> => {
        try {
          const transcriptPath: string = await writeTranscript(sourceUuid, db);

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
          return await exporter.export(filenames, passphrase, sourceName);
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

    const mainWindow = createWindow();

    const fetchWorker = spawnFetchWorker(mainWindow);
  });

  app.on("window-all-closed", () => {
    app.quit();
  });

  app.on("before-quit", () => {
    db.close();
  });
}
