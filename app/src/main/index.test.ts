import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { SyncStatus } from "../types";

const testState = vi.hoisted(() => {
  const registeredHandlers = new Map<string, (...args: unknown[]) => unknown>();
  const workerInstances: MockWorker[] = [];

  class MockWorker {
    on = vi.fn();
    postMessage = vi.fn();
    terminate = vi.fn();

    constructor() {
      workerInstances.push(this);
    }
  }

  class MockBrowserWindow {
    webContents = {
      send: vi.fn(),
      openDevTools: vi.fn(),
    };

    on = vi.fn();
    show = vi.fn();
    loadURL = vi.fn();
    loadFile = vi.fn();
    isDestroyed = vi.fn(() => false);
  }

  return {
    registeredHandlers,
    workerInstances,
    MockWorker,
    MockBrowserWindow,
    app: {
      getVersion: vi.fn(() => "0.0.0-test"),
      requestSingleInstanceLock: vi.fn(() => true),
      whenReady: vi.fn(() => Promise.resolve()),
      on: vi.fn(),
      quit: vi.fn(),
      exit: vi.fn(),
      getLocale: vi.fn(() => "en"),
    },
    dialog: {
      showMessageBox: vi.fn(() => Promise.resolve()),
    },
    ipcMain: {
      handle: vi.fn(
        (channel: string, handler: (...args: unknown[]) => unknown) => {
          registeredHandlers.set(channel, handler);
        },
      ),
    },
    session: {
      defaultSession: {
        webRequest: {
          onHeadersReceived: vi.fn(),
        },
      },
    },
    clipboard: {},
    optimizer: {
      watchWindowShortcuts: vi.fn(),
    },
    is: {
      dev: false,
    },
    syncModule: {
      syncMetadata: vi.fn(),
      shouldSkipSync: vi.fn(),
    },
    proxyJSONRequest: vi.fn(),
    lockRun: vi.fn(async (fn: () => unknown) => await fn()),
    configLoad: vi.fn(() => ({
      sd_submission_key_fpr: "fingerprint",
      is_qubes: false,
      gnupghome: undefined,
      qubes_gpg_domain: undefined,
    })),
    cryptoInitialize: vi.fn(() => ({ mock: "crypto" })),
    datastoreClose: vi.fn(),
    setUmask: vi.fn(),
  };
});

vi.mock("electron", () => ({
  app: testState.app,
  BrowserWindow: testState.MockBrowserWindow,
  dialog: testState.dialog,
  ipcMain: testState.ipcMain,
  session: testState.session,
  clipboard: testState.clipboard,
}));

vi.mock("@electron-toolkit/utils", () => ({
  optimizer: testState.optimizer,
  is: testState.is,
}));

vi.mock("worker_threads", () => ({
  Worker: testState.MockWorker,
}));

vi.mock("./sync", () => testState.syncModule);

vi.mock("./proxy", () => ({
  proxyJSONRequest: testState.proxyJSONRequest,
}));

vi.mock("./sync/lock", () => ({
  Lock: class {
    run = testState.lockRun;
  },
  LockTimeoutError: class LockTimeoutError extends Error {},
}));

vi.mock("./config", () => ({
  Config: {
    load: testState.configLoad,
  },
}));

vi.mock("./crypto", () => ({
  Crypto: {
    initialize: testState.cryptoInitialize,
  },
}));

vi.mock("./datastore", () => ({
  Datastore: class {
    getPendingEvents = vi.fn(() => []);
    close = testState.datastoreClose;
  },
}));

vi.mock("./export", () => ({
  Exporter: class {},
  Printer: class {},
}));

vi.mock("./storage", () => ({
  Storage: class {},
}));

vi.mock("./transcriber", () => ({
  writeTranscript: vi.fn(),
}));

vi.mock("./fetch/worker?modulePath", () => ({
  default: "mock-worker-path",
}));

async function loadMainProcessModule() {
  await import("./index");
  await Promise.resolve();
  await Promise.resolve();
}

function getSyncMetadataHandler() {
  const handler = testState.registeredHandlers.get("syncMetadata");
  expect(handler).toBeDefined();
  return handler as (_event: unknown, request: unknown) => Promise<SyncStatus>;
}

describe("syncMetadata IPC handler", () => {
  beforeEach(() => {
    vi.resetModules();
    testState.registeredHandlers.clear();
    testState.workerInstances.length = 0;

    testState.app.getVersion.mockClear();
    testState.app.requestSingleInstanceLock.mockReturnValue(true);
    testState.app.whenReady.mockResolvedValue(undefined);
    testState.app.on.mockClear();
    testState.app.quit.mockClear();
    testState.app.exit.mockClear();
    testState.app.getLocale.mockReturnValue("en");

    testState.dialog.showMessageBox.mockClear();
    testState.ipcMain.handle.mockClear();
    testState.session.defaultSession.webRequest.onHeadersReceived.mockClear();
    testState.optimizer.watchWindowShortcuts.mockClear();

    testState.syncModule.shouldSkipSync.mockReset();
    testState.syncModule.shouldSkipSync.mockReturnValue(false);
    testState.syncModule.syncMetadata.mockReset();
    testState.syncModule.syncMetadata.mockResolvedValue(
      SyncStatus.NOT_MODIFIED,
    );

    testState.proxyJSONRequest.mockReset();
    testState.lockRun.mockReset();
    testState.lockRun.mockImplementation(
      async (fn: () => unknown) => await fn(),
    );
    testState.configLoad.mockClear();
    testState.cryptoInitialize.mockClear();
    testState.datastoreClose.mockClear();
    testState.setUmask.mockClear();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  it("re-wakes the fetch worker when sync returns NOT_MODIFIED", async () => {
    await loadMainProcessModule();

    const handler = getSyncMetadataHandler();
    const request = {
      authToken: "resume-token",
      hintedVersion: undefined,
    };

    const status = await handler({}, request);

    expect(status).toBe(SyncStatus.NOT_MODIFIED);
    expect(testState.syncModule.shouldSkipSync).toHaveBeenCalledTimes(1);
    expect(testState.syncModule.syncMetadata).toHaveBeenCalledTimes(1);
    expect(testState.workerInstances).toHaveLength(1);
    expect(testState.workerInstances[0]?.postMessage).toHaveBeenCalledWith({
      authToken: "resume-token",
    });
  });

  it("re-wakes the fetch worker on the skip-sync fast path", async () => {
    testState.syncModule.shouldSkipSync.mockReturnValue(true);

    await loadMainProcessModule();

    const handler = getSyncMetadataHandler();
    const request = {
      authToken: "skip-token",
      hintedVersion: "v1",
    };

    const status = await handler({}, request);

    expect(status).toBe(SyncStatus.NOT_MODIFIED);
    expect(testState.syncModule.shouldSkipSync).toHaveBeenCalledTimes(1);
    expect(testState.syncModule.syncMetadata).not.toHaveBeenCalled();
    expect(testState.workerInstances).toHaveLength(1);
    expect(testState.workerInstances[0]?.postMessage).toHaveBeenCalledWith({
      authToken: "skip-token",
    });
  });
});
