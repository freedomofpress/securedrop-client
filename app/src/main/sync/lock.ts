export class Lock {
  private mutex: Promise<void>;

  constructor() {
    this.mutex = Promise.resolve(); // Initially, the lock is available
  }

  /**
   * Acquires the lock. The returned promise resolves when the lock is acquired.
   */
  async acquire(): Promise<() => void> {
    let release: () => void;
    const newMutex = new Promise<void>((resolve) => {
      release = resolve;
    });

    // Wait for the previous operation to finish and then set the new mutex
    const currentMutex = this.mutex;
    this.mutex = newMutex;
    await currentMutex;

    // The lock is now acquired, return the release function
    // @ts-expect-error - release is always assigned before this point
    return release;
  }

  /**
   * Executes a function with the lock acquired, then releases it.
   * @param fn The function to execute while holding the lock.
   */
  async run<T>(fn: () => Promise<T>): Promise<T> {
    const release = await this.acquire();
    try {
      return await fn();
    } finally {
      release();
    }
  }
}
