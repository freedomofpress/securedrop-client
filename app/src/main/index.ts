import "source-map-support/register";
import { app, BrowserWindow, ipcMain } from "electron";
import { join } from "path";
import { optimizer, is } from "@electron-toolkit/utils";
import {
  installExtension,
  REDUX_DEVTOOLS,
  REACT_DEVELOPER_TOOLS,
} from "electron-devtools-installer";

import { DB } from "./database";
import { proxy } from "./proxy";
import type {
  ProxyRequest,
  ProxyResponse,
  Source,
  SourceWithItems,
  Journalist,
  SyncMetadataRequest,
} from "../types";
import { syncMetadata } from "./sync";

const db = new DB();

function createWindow(): void {
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
}

// This method will be called when Electron has finished
// initialization and is ready to create browser windows.
// Some APIs can only be used after this event occurs.
app.whenReady().then(() => {
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

  // Default open or close DevTools by F12 in development
  // and ignore CommandOrControl + R in production.
  // see https://github.com/alex8088/electron-toolkit/tree/master/packages/utils
  app.on("browser-window-created", (_, window) => {
    optimizer.watchWindowShortcuts(window);
  });

  ipcMain.handle(
    "request",
    async (_event, request: ProxyRequest): Promise<ProxyResponse> => {
      const result = await proxy(request);
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

  ipcMain.handle("getJournalists", async (_event): Promise<Journalist[]> => {
    const journalists = db.getJournalists();
    return journalists;
  });

  ipcMain.handle(
    "syncMetadata",
    async (_event, request: SyncMetadataRequest) => {
      await syncMetadata(db, request.authToken);
    },
  );

  ipcMain.handle("getSystemLanguage", async (_event): Promise<string> => {
    const systemLanguage = process.env.LANG || app.getLocale() || "en";
    return systemLanguage;
  });
  createWindow();
});

app.on("window-all-closed", () => {
  app.quit();
});

app.on("before-quit", () => {
  db.close();
});
