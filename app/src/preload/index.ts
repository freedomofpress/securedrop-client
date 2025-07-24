// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from "electron";
import type { ProxyRequest, ProxyResponse, Source, Item } from "../types";

const electronAPI = {
  request: (request: ProxyRequest): Promise<ProxyResponse> =>
    ipcRenderer.invoke("request", request),
  requestStream: (
    request: ProxyRequest,
    downloadPath: string,
  ): Promise<ProxyResponse> =>
    ipcRenderer.invoke("requestStream", request, downloadPath),
  getSources: (): Promise<Source[]> => ipcRenderer.invoke("getSources"),
  getItems: (sourceUuid: string): Promise<Item[]> =>
    ipcRenderer.invoke("getItems", sourceUuid),
};

contextBridge.exposeInMainWorld("electronAPI", electronAPI);

export type ElectronAPI = typeof electronAPI;
