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

  it("should acquire lock successfully with timeout if available immediately", async () => {
    const lock = new Lock();
    const release = await lock.acquire(1000);
    expect(release).toBeDefined();
    release();
  });

  it("should throw error when timeout expires waiting for lock", async () => {
    const lock = new Lock();

    // Acquire the lock and hold it for 200ms
    const firstRelease = await lock.acquire();
    setTimeout(() => firstRelease(), 200);

    // Try to acquire with a 50ms timeout - should fail
    await expect(lock.acquire(50)).rejects.toThrow(
      "Failed to acquire lock within 50ms",
    );
  });

  it("should acquire lock before timeout if released in time", async () => {
    const lock = new Lock();

    // Acquire the lock and hold it for 50ms
    const firstRelease = await lock.acquire();
    setTimeout(() => firstRelease(), 50);

    // Try to acquire with a 200ms timeout - should succeed
    const secondRelease = await lock.acquire(200);
    expect(secondRelease).toBeDefined();
    secondRelease();
  });

  it("should run function successfully with timeout", async () => {
    const lock = new Lock();
    let executed = false;

    await lock.run(async () => {
      executed = true;
    }, 1000);

    expect(executed).toBe(true);
  });

  it("should throw error when run() times out waiting for lock", async () => {
    const lock = new Lock();

    // Start a long-running operation
    const firstPromise = lock.run(async () => {
      await new Promise((res) => setTimeout(res, 200));
    });

    // Try to run with a short timeout - should fail
    const secondPromise = lock.run(async () => {
      return "should not execute";
    }, 50);

    await expect(secondPromise).rejects.toThrow(
      "Failed to acquire lock within 50ms",
    );

    // Wait for first operation to complete
    await firstPromise;
  });
});
