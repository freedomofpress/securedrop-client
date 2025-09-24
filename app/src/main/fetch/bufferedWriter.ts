import { Writable } from "stream";

/// BufferedWriter provides a utility class that implements the Writable interface
/// allowing for data to be streamed directly to a Buffer.
/// This is used by the fetch workers to stream message data to an in-memory Buffer
/// to avoid having to open a temporary file.
export class BufferedWriter extends Writable {
  buffer: Buffer[];
  final: boolean;

  constructor() {
    super();
    this.buffer = [];
    this.final = false;
  }

  _write(
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    chunk: any,
    encoding: BufferEncoding,
    callback: (error?: Error | null) => void,
  ): void {
    this.buffer.push(Buffer.from(chunk, encoding));
    callback();
  }

  _final(callback: (error?: Error | null) => void): void {
    this.final = true;
    callback();
  }

  getBuffer(): Buffer {
    return Buffer.concat(this.buffer);
  }
}
