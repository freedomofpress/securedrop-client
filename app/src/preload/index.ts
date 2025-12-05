// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import {
  type ProxyJSONResponse,
  type ProxyRequest,
  type ProxyResponse,
  type Source,
  type SourceWithItems,
  type Journalist,
  type AuthedRequest,
  Item,
  PendingEventType,
  SyncStatus,
  DeviceStatus,
} from "../types";

// Log the performance of IPC calls
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function logIpcCall<T>(name: string, fn: (...args: any[]) => Promise<T>) {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  return async (...args: any[]): Promise<T> => {
    console.debug(`[IPC] ${name} called`);
    const start = performance.now();
    const result = await fn(...args);
    const end = performance.now();
    const duration = end - start;
    let timeStr;
    if (duration < 1000) {
      timeStr = `${duration.toFixed(2)}ms`;
    } else {
      timeStr = `${(duration / 1000).toFixed(2)}s`;
    }
    console.debug(`[IPC] ${name} finished in ${timeStr}`);
    return result;
  };
}

const electronAPI = {
  request: logIpcCall<ProxyJSONResponse>("request", (request: ProxyRequest) =>
    ipcRenderer.invoke("request", request),
  ),
  requestStream: logIpcCall<ProxyResponse>(
    "requestStream",
    (request: ProxyRequest, downloadPath: string) =>
      ipcRenderer.invoke("requestStream", request, downloadPath),
  ),
  syncMetadata: logIpcCall<SyncStatus>(
    "syncMetadata",
    (request: AuthedRequest) => ipcRenderer.invoke("syncMetadata", request),
  ),
  updateFetchStatus: logIpcCall(
    "updateFetchStatus",
    (itemUuid: string, fetchStatus: number, authToken: string) =>
      ipcRenderer.invoke("updateFetchStatus", itemUuid, fetchStatus, authToken),
  ),
  getSources: logIpcCall<Source[]>("getSources", () =>
    ipcRenderer.invoke("getSources"),
  ),
  getSourceWithItems: logIpcCall<SourceWithItems>(
    "getSourceWithItems",
    (sourceUuid: string) =>
      ipcRenderer.invoke("getSourceWithItems", sourceUuid),
  ),
  getItem: logIpcCall<Item | null>("getItem", (itemUuid: string) =>
    ipcRenderer.invoke("getItem", itemUuid),
  ),
  getJournalists: logIpcCall<Journalist[]>("getJournalists", () =>
    ipcRenderer.invoke("getJournalists"),
  ),
  getSystemLanguage: logIpcCall<string>("getSystemLanguage", () =>
    ipcRenderer.invoke("getSystemLanguage"),
  ),
  addPendingSourceEvent: logIpcCall<bigint>(
    "addPendingSourceEvent",
    (sourceUuid: string, type: PendingEventType) =>
      ipcRenderer.invoke("addPendingSourceEvent", sourceUuid, type),
  ),
  addPendingReplySentEvent: logIpcCall<bigint>(
    "addPendingReplySentEvent",
    (text: string, sourceUuid: string, interactionCount: number) =>
      ipcRenderer.invoke(
        "addPendingReplySentEvent",
        text,
        sourceUuid,
        interactionCount,
      ),
  ),
  addPendingItemEvent: logIpcCall<bigint>(
    "addPendingItemEvent",
    (itemUuid: string, type: PendingEventType) =>
      ipcRenderer.invoke("addPendingItemEvent", itemUuid, type),
  ),
  addPendingItemsSeenBatch: logIpcCall<bigint[]>(
    "addPendingItemsSeenBatch",
    (sourceUuid: string, itemUuids: string[]) =>
      ipcRenderer.invoke("addPendingItemsSeenBatch", sourceUuid, itemUuids),
  ),
  shouldAutoLogin: logIpcCall<boolean>("shouldAutoLogin", () =>
    ipcRenderer.invoke("shouldAutoLogin"),
  ),
  getCSPNonce: logIpcCall<string>("getCSPNonce", () =>
    ipcRenderer.invoke("getCSPNonce"),
  ),
  openFile: logIpcCall<void>("openFile", (itemUuid: string) =>
    ipcRenderer.invoke("openFile", itemUuid),
  ),
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  onItemUpdate: (callback: (...args: any[]) => void) => {
    ipcRenderer.on("item-update", (_event, ...args) => callback(...args));
  },
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  onSourceUpdate: (callback: (...args: any[]) => void) => {
    ipcRenderer.on("source-update", (_event, ...args) => callback(...args));
  },
  clearClipboard: logIpcCall<void>("clearClipboard", () =>
    ipcRenderer.invoke("clearClipboard"),
  ),
  initiateExport: logIpcCall<DeviceStatus>("initiateExport", () =>
    ipcRenderer.invoke("initiateExport"),
  ),
  export: logIpcCall<DeviceStatus>(
    "export",
    (itemUuids: string[], passphrase: string) =>
      ipcRenderer.invoke("export", itemUuids, passphrase),
  ),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
