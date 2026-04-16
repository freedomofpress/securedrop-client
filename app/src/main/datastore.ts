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

  override deleteItems(items: string[]) {
    const FETCH_BATCH_SIZE = 500;
    for (let i = 0; i < items.length; i += FETCH_BATCH_SIZE) {
      const batch = items.slice(i, i + FETCH_BATCH_SIZE);
      const deletedItems = super.getItems(batch);
      for (const item of deletedItems) {
        this.storage.deleteItemFs(item);
      }
    }
    super.deleteItems(items);
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
      void this.storage.deleteItemFs(item);
    }
    return deletedItems;
  }

  override updateSources(sources: {
    [uuid: string]: SourceMetadata | null;
  }): string[] {
    const deletedSourceUuids = super.updateSources(sources);
    for (const uuid of deletedSourceUuids) {
      void this.storage.deleteSourceFs(uuid);
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
      void this.storage.deleteItemFs(item);
    }
    for (const uuid of result.deleted_sources) {
      void this.storage.deleteSourceFs(uuid);
    }
    return result;
  }

  async deleteSourceFs(sourceID: string): Promise<void> {
    return this.storage.deleteSourceFs(sourceID);
  }

  async deleteItemFs(item: Item): Promise<void> {
    return this.storage.deleteItemFs(item);
  }
}
