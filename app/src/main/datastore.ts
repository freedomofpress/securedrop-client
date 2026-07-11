import { DB } from "./database";
import { Storage } from "./storage";
import {
  BatchResponse,
  FilesystemCleanupJob,
  Item,
  ItemMetadata,
  JournalistMetadata,
  SourceMetadata,
  IndexDeletionPlan,
} from "../types";
import { Crypto } from "./crypto";
import { BatchResponseSchema } from "../schemas";

/**
 * Datastore wraps DB and Storage to ensure that deletion operations remove both
 * the DB record and any corresponding files from the filesystem.
 */
export class Datastore extends DB {
  private readonly storage: Storage;
  private readonly DELETE_BATCH_SIZE = 8;
  private cleanupPromise: Promise<void> | null = null;

  constructor(crypto: Crypto, storage: Storage, dbDir?: string) {
    super(crypto, dbDir);
    this.storage = storage;
  }

  async deleteItemsAsync(items: string[]): Promise<Item[]> {
    const deletedItems = super.deleteItems(items);
    await this.runFilesystemCleanupJobs();
    return deletedItems;
  }

  async deleteSourcesAsync(sources: string[]): Promise<void> {
    super.deleteSources(sources);
    await this.runFilesystemCleanupJobs();
  }

  override deleteJournalists(journalists: string[]): void {
    super.deleteJournalists(journalists);
  }

  async cleanupInvalidLifecycleData(): Promise<void> {
    super.removeInvalidLifecycleData();
    await this.runFilesystemCleanupJobs();
  }

  override updateItems(items: { [uuid: string]: ItemMetadata | null }): Item[] {
    return super.updateItems(items);
  }

  override updateSources(sources: {
    [uuid: string]: SourceMetadata | null;
  }): string[] {
    return super.updateSources(sources);
  }

  override updateJournalists(journalists: {
    [uuid: string]: JournalistMetadata | null;
  }): void {
    super.updateJournalists(journalists);
  }

  override updateBatch(
    batchResponse: BatchResponse,
    deletions: IndexDeletionPlan,
  ): {
    deleted_items: Item[];
    deleted_sources: string[];
  } {
    const validatedBatch = BatchResponseSchema.parse(batchResponse);
    const result = super.updateBatch(validatedBatch, deletions);
    void this.runFilesystemCleanupJobs();
    return result;
  }

  runFilesystemCleanupJobs(): Promise<void> {
    const previousCleanup = this.cleanupPromise ?? Promise.resolve();
    const cleanup = previousCleanup.then(() =>
      this.drainFilesystemCleanupJobs(),
    );
    this.cleanupPromise = cleanup;
    void cleanup.then(
      () => this.clearCleanupPromise(cleanup),
      () => this.clearCleanupPromise(cleanup),
    );
    return cleanup;
  }

  private clearCleanupPromise(cleanup: Promise<void>): void {
    if (this.cleanupPromise === cleanup) {
      this.cleanupPromise = null;
    }
  }

  private async drainFilesystemCleanupJobs(): Promise<void> {
    const jobs = super.getPendingFilesystemCleanupJobs();
    for (let i = 0; i < jobs.length; i += this.DELETE_BATCH_SIZE) {
      const batch = jobs.slice(i, i + this.DELETE_BATCH_SIZE);
      await Promise.all(batch.map((job) => this.runFilesystemCleanupJob(job)));
    }
  }

  private async runFilesystemCleanupJob(
    job: FilesystemCleanupJob,
  ): Promise<void> {
    try {
      await this.storage.runFilesystemCleanupJob(job);
      super.completeFilesystemCleanupJob(job.id);
    } catch (error) {
      console.error("Failed to run filesystem cleanup job", {
        job: job.id,
        error,
      });
    }
  }
}
