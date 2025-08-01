import { app, BrowserWindow, ipcMain } from "electron";
import { join } from "path";
import { optimizer, is } from "@electron-toolkit/utils";

import { openDatabase, closeDatabase, runMigrations } from "./database";
import { proxy } from "./proxy";
import type { ProxyRequest } from "../types";

openDatabase();
runMigrations();

function createWindow(): void {
  const mainWindow = new BrowserWindow({
    width: is.dev && process.env["NODE_ENV"] != "production" ? 1200 : 900,
    height: 700,
    minWidth: 900,
    minHeight: 700,
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
  // Default open or close DevTools by F12 in development
  // and ignore CommandOrControl + R in production.
  // see https://github.com/alex8088/electron-toolkit/tree/master/packages/utils
  app.on("browser-window-created", (_, window) => {
    optimizer.watchWindowShortcuts(window);
  });

  ipcMain.handle("request", async (_event, request: ProxyRequest) => {
    const result = await proxy(request);
    return result;
  });

  createWindow();
});

app.on("window-all-closed", () => {
  app.quit();
});

app.on("before-quit", () => {
  closeDatabase();
});
