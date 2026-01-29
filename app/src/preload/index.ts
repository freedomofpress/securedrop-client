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
  onItemUpdate: (callback: (item: Item) => void) => {
    const listener = (_event: Electron.IpcRendererEvent, item: Item) =>
      callback(item);
    ipcRenderer.on("item-update", listener);
    return () => ipcRenderer.removeListener("item-update", listener);
  },
  onSourceUpdate: (callback: (source: Source) => void) => {
    const listener = (_event: Electron.IpcRendererEvent, source: Source) =>
      callback(source);
    ipcRenderer.on("source-update", listener);
    return () => ipcRenderer.removeListener("source-update", listener);
  },
  clearClipboard: logIpcCall<void>("clearClipboard", () =>
    ipcRenderer.invoke("clearClipboard"),
  ),
  initiateExport: logIpcCall<DeviceStatus>("initiateExport", () =>
    ipcRenderer.invoke("initiateExport"),
  ),
  exportTranscript: logIpcCall<DeviceStatus>(
    "exportTranscript",
    (sourceUuid: string, passphrase: string) =>
      ipcRenderer.invoke("exportTranscript", sourceUuid, passphrase),
  ),
  export: logIpcCall<DeviceStatus>(
    "export",
    (itemUuids: string[], passphrase: string) =>
      ipcRenderer.invoke("export", itemUuids, passphrase),
  ),
  exportSource: logIpcCall<DeviceStatus>(
    "exportSource",
    (sourceUuid: string, itemUuids: string[], passphrase: string) =>
      ipcRenderer.invoke("exportSource", sourceUuid, itemUuids, passphrase),
  ),
  initiatePrint: logIpcCall<DeviceStatus>("initiatePrint", () =>
    ipcRenderer.invoke("initiatePrint"),
  ),
  print: logIpcCall<DeviceStatus>("print", (itemUuid: string) =>
    ipcRenderer.invoke("print", itemUuid),
  ),
  printTranscript: logIpcCall<DeviceStatus>(
    "printTranscript",
    (sourceUuid: string) => ipcRenderer.invoke("printTranscript", sourceUuid),
  ),
  cancelExport: logIpcCall<void>("cancelExport", () =>
    ipcRenderer.invoke("cancelExport"),
  ),
  cancelPrint: logIpcCall<void>("cancelPrint", () =>
    ipcRenderer.invoke("cancelPrint"),
  ),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
