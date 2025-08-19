// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import type {
  ProxyJSONResponse,
  ProxyRequest,
  ProxyResponse,
  Source,
  SourceWithItems,
  SyncMetadataRequest,
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
  syncMetadata: logIpcCall("syncMetadata", (request: SyncMetadataRequest) =>
    ipcRenderer.invoke("syncMetadata", request),
  ),
  getSources: logIpcCall<Source[]>(
    "getSources",
    (params?: {
      searchTerm?: string;
      filter?: "all" | "read" | "unread" | "starred" | "unstarred";
      sortedAsc?: boolean;
      limit?: number;
      offset?: number;
    }) => ipcRenderer.invoke("getSources", params),
  ),
  getSourcesCount: logIpcCall<number>(
    "getSourcesCount",
    (params?: {
      searchTerm?: string;
      filter?: "all" | "read" | "unread" | "starred" | "unstarred";
    }) => ipcRenderer.invoke("getSourcesCount", params),
  ),
  getSourceWithItems: logIpcCall<SourceWithItems>(
    "getSourceWithItems",
    (sourceUuid: string) =>
      ipcRenderer.invoke("getSourceWithItems", sourceUuid),
  ),
  getSystemLanguage: logIpcCall<string>("getSystemLanguage", () =>
    ipcRenderer.invoke("getSystemLanguage"),
  ),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
