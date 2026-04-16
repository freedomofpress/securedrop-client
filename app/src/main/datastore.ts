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

  constructor(crypto: Crypto, storage: Storage, dbDir?: string) {
    super(crypto, dbDir);
    this.storage = storage;
  }

  override deleteItems(items: string[]) {
    const DELETE_BATCH_SIZE = 500;
    for (let i = 0; i < items.length; i += DELETE_BATCH_SIZE) {
      const batch = items.slice(i, i + DELETE_BATCH_SIZE);
      const deletedItems = super.getItems(batch);
      super.deleteItems(batch);
      for (const item of deletedItems) {
        this.storage.deleteItemFs(item);
      }
    }
  }

  override deleteSources(sources: string[]): void {
    super.deleteSources(sources);
    for (const uuid of sources) {
      this.storage.deleteSourceFs(uuid);
    }
  }

  override deleteJournalists(journalists: string[]): void {
    super.deleteJournalists(journalists);
  }

  override updateItems(items: { [uuid: string]: ItemMetadata | null }): Item[] {
    const deletedItems = super.updateItems(items);
    for (const item of deletedItems) {
      this.storage.deleteItemFs(item);
    }
    return deletedItems;
  }

  override updateSources(sources: {
    [uuid: string]: SourceMetadata | null;
  }): string[] {
    const deletedSourceUuids = super.updateSources(sources);
    for (const uuid of deletedSourceUuids) {
      this.storage.deleteSourceFs(uuid);
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
      this.storage.deleteItemFs(item);
    }
    for (const uuid of result.deleted_sources) {
      this.storage.deleteSourceFs(uuid);
    }
    return result;
  }

  deleteSourceFs(sourceID: string): void {
    return this.storage.deleteSourceFs(sourceID);
  }

  deleteItemFs(item: Item): void {
    return this.storage.deleteItemFs(item);
  }
}
