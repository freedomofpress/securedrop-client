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

  override deleteItems(items: string[]): Item[] {
    const deletedItems = super.deleteItems(items);
    for (const item of deletedItems) {
      this.storage.deleteItemFs(item);
    }
    return deletedItems;
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
}
