import { describe, it, expect } from "vitest";
import { BufferedWriter } from "./bufferedWriter";

describe("BufferedWriter constructor", () => {
  it("should initialize buffer as an empty array", () => {
    const writer = new BufferedWriter();
    expect(writer.buffer).toEqual([]);
  });

  it("should initialize final as false", () => {
    const writer = new BufferedWriter();
    expect(writer.final).toBe(false);
  });

  it("should add chunks to buffer", () => {
    const writer = new BufferedWriter();
    const chunk = Buffer.from("hello");
    writer.write(chunk, "utf8", () => {
      expect(writer.buffer.length).toBe(1);
      expect(writer.buffer[0].toString()).toBe("hello");
    });
  });

  it("should set final to true", () => {
    const writer = new BufferedWriter();
    writer.end(() => {
      expect(writer.final).toBe(true);
    });
  });

  it("should return error if stream not closed", () => {
    const writer = new BufferedWriter();
    writer.write("data", "utf8", () => {});
    const result = writer.getBuffer();
    expect(result).toBeInstanceOf(Error);
    expect((result as Error).message).toBe(
      "Writable stream not yet closed, cannot return buffer",
    );
  });

  it("should return concatenated buffer after stream is closed", () => {
    const writer = new BufferedWriter();
    writer.write("foo", "utf8", () => {
      writer.write("bar", "utf8", () => {
        writer.end(() => {
          const result = writer.getBuffer();
          expect(Buffer.isBuffer(result)).toBe(true);
          expect((result as Buffer).toString()).toBe("foobar");
        });
      });
    });
  });
});
