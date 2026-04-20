declare module "unix-dgram" {
  import { EventEmitter } from "events";

  class Socket extends EventEmitter {
    connected: boolean;
    send(
      buf: Buffer,
      offset: number,
      length: number,
      path: string,
      callback?: (err?: Error) => void,
    ): void;
    send(buf: Buffer, callback?: (err?: Error) => void): void;
    connect(path: string): void;
    bind(path: string): void;
    close(): void;
  }

  function createSocket(
    type: "unix_dgram",
    listener?: (msg: Buffer) => void,
  ): Socket;
}
