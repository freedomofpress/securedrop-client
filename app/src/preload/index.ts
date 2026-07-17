// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import {
  type ProxyResponse,
  type Source,
  type SourceWithItems,
  type SourceItemCounts,
  type Journalist,
  type SyncRequest,
  type LoginCredentials,
  type LoginResult,
  type SearchResult,
  type FirstRunStatus,
  Item,
  PendingEventType,
  SyncStatus,
  DeviceStatus,
  PendingEventData,
  ProxyRequest,
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
  getAppVersion: logIpcCall<string>("getAppVersion", () =>
    ipcRenderer.invoke("getAppVersion"),
  ),
  quitApp: logIpcCall<string>("quitApp", () => ipcRenderer.invoke("quitApp")),
  login: logIpcCall<LoginResult>("login", (credentials: LoginCredentials) =>
    ipcRenderer.invoke("login", credentials),
  ),
  requestStream: logIpcCall<ProxyResponse>(
    "requestStream",
    (request: ProxyRequest, downloadPath: string) =>
      ipcRenderer.invoke("requestStream", request, downloadPath),
  ),
  syncMetadata: logIpcCall<SyncStatus>("syncMetadata", (request: SyncRequest) =>
    ipcRenderer.invoke("syncMetadata", request),
  ),
  updateFetchStatus: logIpcCall(
    "updateFetchStatus",
    (itemUuid: string, fetchStatus: number) =>
      ipcRenderer.invoke("updateFetchStatus", itemUuid, fetchStatus),
  ),
  getSources: logIpcCall<Record<string, Source>>("getSources", () =>
    ipcRenderer.invoke("getSources"),
  ),
  getSourceWithItems: logIpcCall<SourceWithItems>(
    "getSourceWithItems",
    (
      sourceUuid: string,
      options?: {
        limit?: number;
        beforeInteractionCount?: number;
        journalistUuid?: string;
      },
    ) => ipcRenderer.invoke("getSourceWithItems", sourceUuid, options),
  ),
  getSourceItemCounts: logIpcCall<SourceItemCounts>(
    "getSourceItemCounts",
    (sourceUuids: string[]) =>
      ipcRenderer.invoke("getSourceItemCounts", sourceUuids),
  ),
  getItem: logIpcCall<Item | null>("getItem", (itemUuid: string) =>
    ipcRenderer.invoke("getItem", itemUuid),
  ),
  getJournalists: logIpcCall<Journalist[]>("getJournalists", () =>
    ipcRenderer.invoke("getJournalists"),
  ),
  search: logIpcCall<SearchResult[]>("search", (query: string) =>
    ipcRenderer.invoke("search", query),
  ),
  getSystemLanguage: logIpcCall<string>("getSystemLanguage", () =>
    ipcRenderer.invoke("getSystemLanguage"),
  ),
  getSubmissionKeyFingerprint: logIpcCall<string>(
    "getSubmissionKeyFingerprint",
    () => ipcRenderer.invoke("getSubmissionKeyFingerprint"),
  ),
  addPendingSourceEvent: logIpcCall<string | null>(
    "addPendingSourceEvent",
    (sourceUuid: string, type: PendingEventType, data?: PendingEventData) =>
      ipcRenderer.invoke("addPendingSourceEvent", sourceUuid, type, data),
  ),
  addPendingSourceEventBatch: logIpcCall<(string | null)[]>(
    "addPendingSourceEventBatch",
    (
      events: Array<{
        sourceUuid: string;
        type: PendingEventType;
        data?: PendingEventData;
      }>,
    ) => ipcRenderer.invoke("addPendingSourceEventBatch", events),
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
  addPendingItemEvent: logIpcCall<string | null>(
    "addPendingItemEvent",
    (itemUuid: string, type: PendingEventType) =>
      ipcRenderer.invoke("addPendingItemEvent", itemUuid, type),
  ),
  addPendingSourceConversationSeen: logIpcCall<string | null>(
    "addPendingSourceConversationSeen",
    (sourceUuid: string, upperBound: number) =>
      ipcRenderer.invoke(
        "addPendingSourceConversationSeen",
        sourceUuid,
        upperBound,
      ),
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
  onSyncComplete: (callback: (status: SyncStatus) => void) => {
    const listener = (_event: Electron.IpcRendererEvent, status: SyncStatus) =>
      callback(status);
    ipcRenderer.on("sync-complete", listener);
    return () => ipcRenderer.removeListener("sync-complete", listener);
  },
  onQuitRequested: (callback: () => void) => {
    const listener = () => callback();
    ipcRenderer.on("quit-requested", listener);
    return () => ipcRenderer.removeListener("quit-requested", listener);
  },
  clearClipboard: logIpcCall<void>("clearClipboard", () =>
    ipcRenderer.invoke("clearClipboard"),
  ),
  initiateExport: logIpcCall<DeviceStatus>("initiateExport", () =>
    ipcRenderer.invoke("initiateExport"),
  ),
  exportTranscript: logIpcCall<DeviceStatus>(
    "exportTranscript",
    (sourceUuid: string, passphrase: string, whistleflow?: boolean) =>
      ipcRenderer.invoke(
        "exportTranscript",
        sourceUuid,
        passphrase,
        whistleflow,
      ),
  ),
  export: logIpcCall<DeviceStatus>(
    "export",
    (itemUuids: string[], passphrase: string, whistleflow?: boolean) =>
      ipcRenderer.invoke("export", itemUuids, passphrase, whistleflow),
  ),
  exportSource: logIpcCall<DeviceStatus>(
    "exportSource",
    (sourceUuid: string, passphrase: string, whistleflow?: boolean) =>
      ipcRenderer.invoke("exportSource", sourceUuid, passphrase, whistleflow),
  ),
  getWhistleflowEnabled: logIpcCall<boolean>("getWhistleflowEnabled", () =>
    ipcRenderer.invoke("getWhistleflowEnabled"),
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
  getFirstRunStatus: logIpcCall<FirstRunStatus>("getFirstRunStatus", () =>
    ipcRenderer.invoke("getFirstRunStatus"),
  ),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
