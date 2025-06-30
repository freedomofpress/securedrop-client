import { app, BrowserWindow, ipcMain } from "electron";
import path from "node:path";

import { openDatabase, closeDatabase } from "./database";

// eslint-disable-next-line @typescript-eslint/no-unused-vars
const db = openDatabase();

let loginWindow: BrowserWindow | null;
let sourceviewWindow: BrowserWindow | null;

function createLoginWindow() {
  loginWindow = new BrowserWindow({
    width: 400,
    height: 600,
    webPreferences: {
      preload: path.join(__dirname, "preload.js"),
      contextIsolation: true,
    },
  });
  loginWindow.on("closed", () => {
    loginWindow = null;
  });

  if (LOGIN_VITE_DEV_SERVER_URL) {
    loginWindow.loadURL(LOGIN_VITE_DEV_SERVER_URL);
  } else {
    loginWindow.loadFile(
      path.join(__dirname, `../renderer/${LOGIN_VITE_NAME}/login.html`),
    );
  }
  //do we wanna kill it altogether or just hide it?
  loginWindow.on("closed", () => {
    loginWindow = null;
  });
}

function createSourceviewWindow() {
  // Create the source view browser window.
  sourceviewWindow = new BrowserWindow({
    width: 800,
    height: 600,
    show: false,
    webPreferences: {
      preload: path.join(__dirname, "preload.js"),
      contextIsolation: true,
    },
  });

  // and load the source view.
  if (SOURCEVIEW_VITE_DEV_SERVER_URL) {
    sourceviewWindow.loadURL(SOURCEVIEW_VITE_DEV_SERVER_URL);
  } else {
    sourceviewWindow.loadFile(
      path.join(__dirname, `../renderer/${SOURCEVIEW_VITE_NAME}/index.html`),
    );
  }

  // Same question
  sourceviewWindow.on("closed", () => {
    sourceviewWindow = null;
  });
}

// This method will be called when Electron has finished
// initialization and is ready to create browser windows.
// Some APIs can only be used after this event occurs.
app.whenReady().then(() => {
  createLoginWindow();
});

// Handle login success from renderer process
ipcMain.on("login-success", () => {
  if (loginWindow) {
    loginWindow.close(); // Close login window
  }
  createSourceviewWindow();
  if (sourceviewWindow) {
    sourceviewWindow.show(); // Show main window after login
  }
});

app.on("activate", () => {
  if (BrowserWindow.getAllWindows().length === 0) {
    createLoginWindow();
  }
});

// Quit when all windows are closed
app.on("window-all-closed", () => {
  app.quit();
});

app.on("before-quit", () => {
  closeDatabase();
});
