import { Writable } from "stream";

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

  getBuffer(): Buffer | Error {
    if (this.final) {
      return Buffer.concat(this.buffer);
    }
    return new Error("Writable stream not yet closed, cannot return buffer");
  }
}
