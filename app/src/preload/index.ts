// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import type { ProxyRequest } from "../types";

const electronAPI = {
  request: (request: ProxyRequest) => ipcRenderer.invoke("request", request),
  requestStream: (request: ProxyRequest, downloadPath: string) =>
    ipcRenderer.invoke("requestStream", request, downloadPath),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
