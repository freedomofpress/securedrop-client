export class Lock {
  private mutex: Promise<void>;

  constructor() {
    this.mutex = Promise.resolve(); // Initially, the lock is available
  }

  /**
   * Acquires the lock. The returned promise resolves when the lock is acquired.
   * @param timeout Optional timeout in milliseconds. If provided and the lock cannot be acquired within this time, throws an error.
   */
  async acquire(timeout?: number): Promise<() => void> {
    let release: () => void;
    const newMutex = new Promise<void>((resolve) => {
      release = resolve;
    });

    // Wait for the previous operation to finish and then set the new mutex
    const currentMutex = this.mutex;
    this.mutex = newMutex;

    if (timeout !== undefined) {
      const timeoutPromise = new Promise<never>((_, reject) => {
        setTimeout(() => {
          reject(new Error(`Failed to acquire lock within ${timeout}ms`));
        }, timeout);
      });

      try {
        await Promise.race([currentMutex, timeoutPromise]);
      } catch (error) {
        // On timeout, release the mutex so subsequent acquires don't block forever
        // @ts-expect-error - release is always assigned before this point
        release();
        throw error;
      }
    } else {
      await currentMutex;
    }

    // The lock is now acquired, return the release function
    // @ts-expect-error - release is always assigned before this point
    return release;
  }

  /**
   * Executes a function with the lock acquired, then releases it.
   * @param fn The function to execute while holding the lock.
   * @param timeout Optional timeout in milliseconds for acquiring the lock.
   */
  async run<T>(fn: () => Promise<T>, timeout?: number): Promise<T> {
    const release = await this.acquire(timeout);
    try {
      return await fn();
    } finally {
      release();
    }
  }
}
