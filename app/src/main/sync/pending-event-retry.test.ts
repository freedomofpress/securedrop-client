import fs from "fs";
import os from "os";
import path from "path";

import { afterEach, beforeAll, describe, expect, it, vi } from "vitest";

import { Crypto } from "../../../src/main/crypto";
import { Datastore } from "../../../src/main/datastore";
import * as proxyModule from "../../../src/main/proxy";
import { Storage } from "../../../src/main/storage";
import { syncMetadata } from "../../../src/main/sync";
import {
  PendingEvent,
  PendingEventType,
  ProxyJSONResponse,
  SourceMetadata,
  SyncStatus,
} from "../../../src/types";

const SOURCE_UUID = "550e8400-e29b-41d4-a716-446655440001";
type EventResponses = Record<string, [number, string | null]>;
type RetryRow = {
  retry_attempts: number;
  last_event_status: number | null;
};

function sourceMetadata(): SourceMetadata {
  return {
    uuid: SOURCE_UUID,
    journalist_designation: "amber river",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    last_updated: "2026-01-01T00:00:00Z",
    public_key: "public key",
    fingerprint: "fingerprint",
  };
}

describe("pending event retry scheduling", () => {
  let crypto: Crypto;
  let db: Datastore | undefined;
  let dbDir: string | undefined;

  beforeAll(() => {
    (Crypto as unknown as { instance?: Crypto }).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  });

  afterEach(() => {
    vi.restoreAllMocks();
    db?.close();
    db = undefined;
    if (dbDir) {
      fs.rmSync(dbDir, { recursive: true, force: true });
      dbDir = undefined;
    }
  });

  function createDatastore(): Datastore {
    dbDir = fs.mkdtempSync(path.join(os.tmpdir(), "pending-event-retry-"));
    db = new Datastore(crypto, new Storage(), dbDir);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    return db;
  }

  function addPendingEvent(type: PendingEventType): string {
    const eventId = db!.addPendingSourceEvent(SOURCE_UUID, type);
    expect(eventId).not.toBeNull();
    return eventId!;
  }

  function getRetryRow(eventId: string): RetryRow | undefined {
    return db!
      [
        "db"
      ]!.prepare("SELECT retry_attempts, last_event_status FROM pending_events WHERE snowflake_id = ?")
      .get(eventId) as RetryRow | undefined;
  }

  async function runMainFlushLoop(eventResponses: EventResponses) {
    let batchRequests = 0;
    vi.spyOn(proxyModule, "proxyJSONRequest").mockImplementation(
      async (request): Promise<ProxyJSONResponse> => {
        if (request.method === "GET") {
          return {
            status: 304,
            error: false,
            data: null,
            headers: new Map(),
          };
        }
        batchRequests += 1;
        return {
          status: 200,
          error: false,
          data: {
            sources: {},
            items: {},
            journalists: {},
            events: eventResponses,
          },
          headers: new Map(),
        };
      },
    );

    let syncStatus = SyncStatus.NOT_MODIFIED;
    let syncCycles = 0;
    do {
      syncStatus = await syncMetadata(db!, "token");
      syncCycles += 1;
    } while (
      syncStatus === SyncStatus.UPDATED &&
      db!.getPendingEvents().length > 0 &&
      syncCycles < 3
    );

    return { batchRequests, syncCycles, syncStatus };
  }

  function applySubmittedStatuses(
    statuses: EventResponses,
    submittedEvents: PendingEvent[],
  ): void {
    db!.updatePendingEvents(statuses, submittedEvents);
  }

  it("stops the main flush condition after a retained failure", async () => {
    createDatastore();
    const eventId = addPendingEvent(PendingEventType.Starred);
    const result = await runMainFlushLoop({ [eventId]: [500, "retry"] });

    expect(result).toEqual({
      batchRequests: 1,
      syncCycles: 1,
      syncStatus: SyncStatus.UPDATED,
    });
    expect(db!.getPendingEvents()).toEqual([]);
    expect(getRetryRow(eventId)).toEqual({
      retry_attempts: 1,
      last_event_status: 500,
    });
  });

  it("backs off a submitted event when its status is omitted", async () => {
    createDatastore();
    const eventId = addPendingEvent(PendingEventType.Starred);
    const result = await runMainFlushLoop({});

    expect(result).toEqual({
      batchRequests: 1,
      syncCycles: 1,
      syncStatus: SyncStatus.UPDATED,
    });
    expect(db!.getPendingEvents()).toEqual([]);
    expect(getRetryRow(eventId)).toEqual({
      retry_attempts: 1,
      last_event_status: null,
    });
  });

  it("ignores an unrelated status and backs off the submitted event", async () => {
    createDatastore();
    const eventId = addPendingEvent(PendingEventType.Starred);
    const result = await runMainFlushLoop({ 999: [500, "unrelated"] });

    expect(result).toEqual({
      batchRequests: 1,
      syncCycles: 1,
      syncStatus: SyncStatus.UPDATED,
    });
    expect(getRetryRow(eventId)).toEqual({
      retry_attempts: 1,
      last_event_status: null,
    });
    expect(getRetryRow("999")).toBeUndefined();
  });

  it("ignores an unsolicited status targeting an excluded 208 event", async () => {
    createDatastore();
    const excludedEventId = addPendingEvent(PendingEventType.Starred);
    const submitted = db!.getPendingEvents();
    applySubmittedStatuses({ [excludedEventId]: [208, null] }, submitted);
    const submittedEventId = addPendingEvent(PendingEventType.Unstarred);

    expect(db!.getPendingEvents().map((event) => event.id)).toEqual([
      submittedEventId,
    ]);
    const result = await runMainFlushLoop({
      [submittedEventId]: [200, null],
      [excludedEventId]: [500, "unsolicited"],
    });

    expect(result).toEqual({
      batchRequests: 1,
      syncCycles: 1,
      syncStatus: SyncStatus.UPDATED,
    });
    expect(getRetryRow(excludedEventId)).toEqual({
      retry_attempts: 0,
      last_event_status: 208,
    });
    expect(getRetryRow(submittedEventId)).toBeUndefined();
  });
});
