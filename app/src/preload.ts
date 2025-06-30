// See the Electron documentation for details on how to use preload scripts:
// https://www.electronjs.org/docs/latest/tutorial/process-model#preload-scripts

// TODO: figure out if require is safe here
// eslint-disable-next-line @typescript-eslint/no-require-imports
const { contextBridge, ipcRenderer } = require("electron");

// TODO: what types can the channel data be? linter complains if "any"
contextBridge.exposeInMainWorld("the_api", {
  // send: (channel: string, data: any) => ipcRenderer.send(channel, data),
  // on: (channel: string, func: (...args: any[]) => void) => ipcRenderer.on(channel, func),
  send: (channel: string, data: string) => ipcRenderer.send(channel, data),
  on: (channel: string, func: (...args: string[]) => void) =>
    ipcRenderer.on(channel, func),
});
