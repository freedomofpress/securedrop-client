import { DB } from "./database";
import { Storage } from "./storage";
import {
  BatchResponse,
  Item,
  ItemMetadata,
  JournalistMetadata,
  SourceMetadata,
} from "../types";
import { Crypto } from "./crypto";

/**
 * Datastore wraps DB and Storage to ensure that deletion operations remove both
 * the DB record and any corresponding files from the filesystem.
 */
export class Datastore extends DB {
  private readonly storage: Storage;
  private readonly DELETE_BATCH_SIZE = 8;

  constructor(crypto: Crypto, storage: Storage, dbDir?: string) {
    super(crypto, dbDir);
    this.storage = storage;
  }

  private deleteItemFsInBackground(item: Item): void {
    void this.storage.deleteItemFs(item).catch((error: unknown) => {
      console.error("Background item filesystem cleanup failed", {
        item: item.uuid,
        error,
      });
    });
  }

  private deleteSourceFsInBackground(sourceUuid: string): void {
    void this.storage.deleteSourceFs(sourceUuid).catch((error: unknown) => {
      console.error("Background source filesystem cleanup failed", {
        sourceUuid,
        error,
      });
    });
  }

  async deleteItemsAsync(items: string[]): Promise<Item[]> {
    const deletedItems = super.deleteItems(items);
    // TODO: Consider routing FS deletions to the fetch worker so that FS I/O
    // never runs on the main process event loop.
    for (let i = 0; i < deletedItems.length; i += this.DELETE_BATCH_SIZE) {
      const batch = deletedItems.slice(i, i + this.DELETE_BATCH_SIZE);
      await Promise.all(batch.map((item) => this.storage.deleteItemFs(item)));
    }
    return deletedItems;
  }

  async deleteSourcesAsync(sources: string[]): Promise<void> {
    super.deleteSources(sources);
    for (let i = 0; i < sources.length; i += this.DELETE_BATCH_SIZE) {
      const batch = sources.slice(i, i + this.DELETE_BATCH_SIZE);
      await Promise.all(
        batch.map((source) => this.storage.deleteSourceFs(source)),
      );
    }
  }

  override deleteJournalists(journalists: string[]): void {
    super.deleteJournalists(journalists);
  }

  override updateItems(items: { [uuid: string]: ItemMetadata | null }): Item[] {
    const deletedItems = super.updateItems(items);
    for (const item of deletedItems) {
      this.deleteItemFsInBackground(item);
    }
    return deletedItems;
  }

  override updateSources(sources: {
    [uuid: string]: SourceMetadata | null;
  }): string[] {
    const deletedSourceUuids = super.updateSources(sources);
    for (const uuid of deletedSourceUuids) {
      this.deleteSourceFsInBackground(uuid);
    }
    return deletedSourceUuids;
  }

  override updateJournalists(journalists: {
    [uuid: string]: JournalistMetadata | null;
  }): void {
    super.updateJournalists(journalists);
  }

  override updateBatch(batchResponse: BatchResponse): {
    deleted_items: Item[];
    deleted_sources: string[];
  } {
    // Perform all DB updates
    const result = super.updateBatch(batchResponse);
    // Perform all filesystem cleanups as necessary
    for (const item of result.deleted_items) {
      this.deleteItemFsInBackground(item);
    }
    for (const uuid of result.deleted_sources) {
      this.deleteSourceFsInBackground(uuid);
    }
    return result;
  }

  async deleteSourceFs(sourceID: string): Promise<void> {
    return this.storage.deleteSourceFs(sourceID);
  }

  async deleteItemFs(item: Item): Promise<void> {
    return this.storage.deleteItemFs(item);
  }

  async runPendingSourceCleanup(snowflakeId: string): Promise<number> {
    let deletedCount = 0;
    while (true) {
      const cleanup = super.getPendingSourceCleanup(snowflakeId);
      if (!cleanup) {
        return deletedCount;
      }
      for (
        let i = 0;
        i < cleanup.itemUuids.length;
        i += this.DELETE_BATCH_SIZE
      ) {
        const batch = cleanup.itemUuids.slice(i, i + this.DELETE_BATCH_SIZE);
        await Promise.all(
          batch.map((itemUuid) =>
            this.storage.deleteItemDirectory(cleanup.sourceUuid, itemUuid),
          ),
        );
      }
      deletedCount = cleanup.itemUuids.length;
      if (super.finishPendingSourceCleanup(snowflakeId, cleanup.itemUuids)) {
        return deletedCount;
      }
    }
  }
}
