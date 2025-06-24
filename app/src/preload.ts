// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts
import { contextBridge, ipcRenderer } from 'electron'
import { ProxyRequest } from '././proxy';

contextBridge.exposeInMainWorld('electronAPI', {
  request: (request: ProxyRequest) => ipcRenderer.invoke('request', request),
});
