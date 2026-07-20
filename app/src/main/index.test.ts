import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { PendingEventType, SyncStatus } from "../types";

const testState = vi.hoisted(() => {
  const registeredHandlers = new Map<string, (...args: unknown[]) => unknown>();
  const workerInstances: MockWorker[] = [];
  const datastoreInstances: MockDatastore[] = [];

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

  class MockDatastore {
    item = {
      uuid: "item1",
      data: { kind: "message", source: "source1" },
      plaintext: null,
      filename: null,
      fetch_status: 0,
      fetch_progress: null,
      decrypted_size: null,
    };
    getPendingEvents = vi.fn(() => []);
    getItem = vi.fn(() => this.item);
    addPendingItemEvent = vi.fn(
      (_itemUuid: string, _type: unknown): string | null =>
        "pending-item-delete",
    );
    deleteItemFs = vi.fn(async () => undefined);
    close = testState.datastoreClose;

    constructor() {
      datastoreInstances.push(this);
    }
  }

  return {
    registeredHandlers,
    workerInstances,
    datastoreInstances,
    MockWorker,
    MockBrowserWindow,
    MockDatastore,
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
    mockSleep: vi.fn(),
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
  Datastore: testState.MockDatastore,
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

vi.mock("./timeouts", () => ({
  sleep: (...args: unknown[]) => testState.mockSleep(...args),
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

function getAddPendingItemEventHandler() {
  const handler = testState.registeredHandlers.get("addPendingItemEvent");
  expect(handler).toBeDefined();
  return handler as (
    _event: unknown,
    itemUuid: string,
    type: PendingEventType,
  ) => Promise<string | null>;
}

async function loginWithToken(token: string) {
  testState.proxyJSONRequest.mockResolvedValueOnce({
    status: 200,
    error: false,
    data: {
      token,
      expiration: "2025-07-16T19:25:44.388054+00:00",
      journalist_uuid: "7f19192d-c8e3-4518-9d4a-26cb39bc8662",
      journalist_first_name: null,
      journalist_last_name: null,
      hints: { version: "abc123", sources: 0, items: 0 },
    },
    headers: {},
  });
  const loginHandler = testState.registeredHandlers.get("login");
  expect(loginHandler).toBeDefined();
  await loginHandler!(
    {},
    {
      username: "user",
      passphrase: "passphrase",
      oneTimeCode: "123456",
    },
  );
}

describe("syncMetadata IPC handler", () => {
  beforeEach(() => {
    vi.resetModules();
    testState.registeredHandlers.clear();
    testState.workerInstances.length = 0;
    testState.datastoreInstances.length = 0;

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
    testState.mockSleep.mockReset();
    testState.mockSleep.mockResolvedValue(undefined);
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
    await loginWithToken("resume-token");

    const handler = getSyncMetadataHandler();
    const status = await handler({}, { hintedVersion: undefined });

    expect(status).toBe(SyncStatus.NOT_MODIFIED);
    expect(testState.syncModule.shouldSkipSync).toHaveBeenCalledTimes(1);
    expect(testState.syncModule.syncMetadata).toHaveBeenCalledTimes(1);
    expect(testState.workerInstances).toHaveLength(1);
    expect(testState.workerInstances[0]?.postMessage).toHaveBeenCalledWith({
      type: "authedRequest",
      request: {
        authToken: "resume-token",
      },
    });
  });

  it("re-wakes the fetch worker on the skip-sync fast path", async () => {
    testState.syncModule.shouldSkipSync.mockReturnValue(true);

    await loadMainProcessModule();
    await loginWithToken("skip-token");

    const handler = getSyncMetadataHandler();
    const status = await handler({}, { hintedVersion: "v1" });

    expect(status).toBe(SyncStatus.NOT_MODIFIED);
    expect(testState.syncModule.shouldSkipSync).toHaveBeenCalledTimes(1);
    expect(testState.syncModule.syncMetadata).not.toHaveBeenCalled();
    expect(testState.workerInstances).toHaveLength(1);
    expect(testState.workerInstances[0]?.postMessage).toHaveBeenCalledWith({
      type: "authedRequest",
      request: {
        authToken: "skip-token",
      },
    });
  });

  it("retries syncMetadata up to MAX_SYNC_RETRIES times then re-throws", async () => {
    const err = new Error("network failure");
    testState.syncModule.syncMetadata.mockRejectedValue(err);

    await loadMainProcessModule();
    await loginWithToken("retry-token");

    const handler = getSyncMetadataHandler();
    await expect(handler({}, {})).rejects.toThrow("network failure");

    // 1 initial attempt + 3 retries = 4 total calls
    expect(testState.syncModule.syncMetadata).toHaveBeenCalledTimes(4);
    // sleep called between each attempt (not after the final failure)
    expect(testState.mockSleep).toHaveBeenCalledTimes(3);
  });

  it("waits with exponential backoff between retries", async () => {
    const err = new Error("network failure");
    // Fail 3 times then succeed on the 4th attempt
    testState.syncModule.syncMetadata
      .mockRejectedValueOnce(err)
      .mockRejectedValueOnce(err)
      .mockRejectedValueOnce(err)
      .mockResolvedValueOnce(SyncStatus.NOT_MODIFIED);

    await loadMainProcessModule();
    await loginWithToken("backoff-token");

    const handler = getSyncMetadataHandler();
    const status = await handler({}, {});

    expect(status).toBe(SyncStatus.NOT_MODIFIED);
    expect(testState.syncModule.syncMetadata).toHaveBeenCalledTimes(4);
    expect(testState.mockSleep).toHaveBeenCalledTimes(3);
    // backoffMs = 1000 * 2^retryCount where retryCount is post-increment (1, 2, 3)
    expect(testState.mockSleep).toHaveBeenNthCalledWith(1, 2000);
    expect(testState.mockSleep).toHaveBeenNthCalledWith(2, 4000);
    expect(testState.mockSleep).toHaveBeenNthCalledWith(3, 8000);
  });

  it("records item deletion before cancelling worker work and deleting files", async () => {
    await loadMainProcessModule();
    await loginWithToken("delete-token");

    const db = testState.datastoreInstances[0]!;
    const worker = testState.workerInstances[0]!;
    worker.postMessage.mockClear();

    const handler = getAddPendingItemEventHandler();
    const result = await handler({}, "item1", PendingEventType.ItemDeleted);

    expect(result).toBe("pending-item-delete");
    expect(db.getItem).toHaveBeenCalledWith("item1");
    expect(db.addPendingItemEvent).toHaveBeenCalledWith(
      "item1",
      PendingEventType.ItemDeleted,
    );
    expect(worker.postMessage).toHaveBeenCalledWith({
      type: "cancel",
      itemId: "item1",
    });
    expect(db.deleteItemFs).toHaveBeenCalledWith(db.item);

    const addOrder = db.addPendingItemEvent.mock.invocationCallOrder[0]!;
    const cancelCallIndex = worker.postMessage.mock.calls.findIndex(
      ([message]) => (message as { type?: string }).type === "cancel",
    );
    expect(cancelCallIndex).toBeGreaterThanOrEqual(0);
    const cancelOrder =
      worker.postMessage.mock.invocationCallOrder[cancelCallIndex]!;
    const deleteOrder = db.deleteItemFs.mock.invocationCallOrder[0]!;
    expect(addOrder).toBeLessThan(cancelOrder);
    expect(addOrder).toBeLessThan(deleteOrder);
  });

  it("does not cancel worker work or delete files when item deletion is rejected", async () => {
    await loadMainProcessModule();
    await loginWithToken("delete-token");

    const db = testState.datastoreInstances[0]!;
    const worker = testState.workerInstances[0]!;
    db.addPendingItemEvent.mockReturnValue(null);
    worker.postMessage.mockClear();

    const handler = getAddPendingItemEventHandler();
    const result = await handler({}, "item1", PendingEventType.ItemDeleted);

    expect(result).toBeNull();
    expect(worker.postMessage).not.toHaveBeenCalledWith({
      type: "cancel",
      itemId: "item1",
    });
    expect(db.deleteItemFs).not.toHaveBeenCalled();
  });
});
