// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import type { ProxyRequest, SyncMetadataRequest } from "../types";

const electronAPI = {
  request: (request: ProxyRequest) => ipcRenderer.invoke("request", request),
  requestStream: (request: ProxyRequest, downloadPath: string) =>
    ipcRenderer.invoke("request", request, downloadPath),
  syncMetadata: (request: SyncMetadataRequest) =>
    ipcRenderer.invoke("syncMetadata", request),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
