import { describe, it, expect } from "vitest";
import { Lock } from "./lock";

describe("Lock", () => {
  it("should allow acquiring and releasing the lock", async () => {
    const lock = new Lock();
    let acquired = false;
    const release = await lock.acquire();
    acquired = true;
    expect(acquired).toBe(true);
    release();
  });

  it("should serialize concurrent acquire calls", async () => {
    const lock = new Lock();
    const order: string[] = [];

    const first = lock.acquire().then((release) => {
      order.push("first");
      setTimeout(() => {
        release();
        order.push("first released");
      }, 50);
    });

    const second = lock.acquire().then((release) => {
      order.push("second");
      release();
      order.push("second released");
    });

    await Promise.all([first, second]);
    expect(order).toEqual([
      "first",
      "first released",
      "second",
      "second released",
    ]);
  });

  it("should run functions in sequence using run()", async () => {
    const lock = new Lock();
    const result: number[] = [];

    await Promise.all([
      lock.run(async () => {
        result.push(1);
        await new Promise((res) => setTimeout(res, 30));
        result.push(2);
      }),
      lock.run(async () => {
        result.push(3);
        await new Promise((res) => setTimeout(res, 10));
        result.push(4);
      }),
    ]);

    expect(result).toEqual([1, 2, 3, 4]);
  });

  it("should release the lock even if the function throws", async () => {
    const lock = new Lock();
    let errorCaught = false;

    await expect(
      lock.run(async () => {
        throw new Error("fail");
      }),
    ).rejects.toThrow("fail");

    // Should be able to acquire again
    await lock.run(async () => {
      errorCaught = true;
    });

    expect(errorCaught).toBe(true);
  });
});
