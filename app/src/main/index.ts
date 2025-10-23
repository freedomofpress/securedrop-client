import "source-map-support/register";
import { app, BrowserWindow, ipcMain, session } from "electron";
import { join } from "path";
import { randomBytes } from "crypto";
import { optimizer, is } from "@electron-toolkit/utils";
import {
  installExtension,
  REDUX_DEVTOOLS,
  REACT_DEVELOPER_TOOLS,
} from "electron-devtools-installer";
import { Worker } from "worker_threads";

import { DB } from "./database";
import { Crypto, CryptoConfig } from "./crypto";
import { proxyJSONRequest } from "./proxy";
import type {
  ProxyRequest,
  ProxyResponse,
  Source,
  SourceWithItems,
  Journalist,
  AuthedRequest,
  Item,
  PendingEventType,
  SyncStatus,
} from "../types";
import { syncMetadata } from "./sync";
import workerPath from "./fetch/worker?modulePath";
import { Lock } from "./sync/lock";
import { Config } from "./config";

// Parse command line arguments
const args = process.argv.slice(2);
const noQubes = args.includes("--no-qubes");
const shouldAutoLogin = args.includes("--login");

const config = Config.load(noQubes);

// Create crypto config + initialize
const cryptoConfig: CryptoConfig = {
  journalistPublicKey: config.journalist_public_key,
  isQubes: config.is_qubes,
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
      sandbox: false,
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
    mainWindow.webContents.send("item-update", result);
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

  ipcMain.handle("getItem", async (_event, itemUuid: string): Promise<Item> => {
    return db.getItem(itemUuid);
  });

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
      db.updateFetchStatus(itemUuid, fetchStatus);
      fetchWorker.postMessage({
        authToken: authToken,
      } as AuthedRequest);
    },
  );

  ipcMain.handle(
    "syncMetadata",
    async (_event, request: AuthedRequest): Promise<SyncStatus> => {
      const syncStatus = await syncLock.run(async () => {
        return await syncMetadata(db, request.authToken);
      });
      // Send message to fetch worker to fetch newly synced items, if any
      fetchWorker.postMessage({
        authToken: request.authToken,
      } as AuthedRequest);
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

  const mainWindow = createWindow();

  const fetchWorker = spawnFetchWorker(mainWindow);
});

app.on("window-all-closed", () => {
  app.quit();
});

app.on("before-quit", () => {
  db.close();
});
