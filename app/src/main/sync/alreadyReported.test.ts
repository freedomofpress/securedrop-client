import fs from "fs";
import os from "os";
import path from "path";
import {
  afterEach,
  beforeAll,
  beforeEach,
  describe,
  expect,
  it,
  MockInstance,
  vi,
} from "vitest";

import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import * as proxyModule from "../proxy";
import { Storage } from "../storage";
import { syncMetadata } from ".";
import {
  BatchResponse,
  ItemMetadata,
  PendingEventType,
  SourceMetadata,
} from "../../types";

const SOURCE_UUID = "550e8400-e29b-41d4-a716-446655440001";
const ITEM_UUID = "660e8400-e29b-41d4-a716-446655440001";
const IDEMPOTENCE_PERIOD_SECONDS = 24 * 60 * 60;

type PendingEventRetryState = {
  retry_attempts: number;
  retry_delay_seconds: number;
};

function sourceMetadata(): SourceMetadata {
  return {
    uuid: SOURCE_UUID,
    journalist_designation: "source alpha",
    is_starred: false,
    is_seen: false,
    has_attachment: true,
    last_updated: "2026-07-07T00:00:00Z",
    public_key: "fake-key",
    fingerprint: "fake-fingerprint",
  };
}

function itemMetadata(): ItemMetadata {
  return {
    uuid: ITEM_UUID,
    source: SOURCE_UUID,
    kind: "message",
    size: 42,
    is_read: false,
    seen_by: [],
    interaction_count: 1,
  };
}

function responseWithStatus(eventId: string, status: number): BatchResponse {
  return {
    sources: {},
    items: {},
    journalists: {},
    events: { [eventId]: [status, null] },
  };
}

function queueSyncResponse(
  proxyMock: MockInstance,
  batchResponse: BatchResponse,
): void {
  proxyMock
    .mockResolvedValueOnce({
      status: 304,
      error: false,
      data: null,
      headers: new Map(),
    })
    .mockResolvedValueOnce({
      status: 200,
      error: false,
      data: batchResponse,
      headers: new Map(),
    });
}

describe("AlreadyReported sync retry", () => {
  let crypto: Crypto;
  let db: Datastore;
  let testHome: string;

  beforeAll(() => {
    (Crypto as any).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  });

  beforeEach(() => {
    testHome = fs.mkdtempSync(path.join(os.tmpdir(), "already-reported-sync-"));
    vi.spyOn(os, "homedir").mockReturnValue(testHome);
    db = new Datastore(crypto, new Storage(), path.join(testHome, "database"));
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({ [ITEM_UUID]: itemMetadata() });
  });

  afterEach(() => {
    db.close();
    vi.restoreAllMocks();
    fs.rmSync(testHome, { recursive: true, force: true });
  });

  it("reuses the event ID through the completed-key retention period", async () => {
    const eventId = db.addPendingSourceEvent(
      SOURCE_UUID,
      PendingEventType.SourceDeleted,
    )!;
    const proxyMock = vi.spyOn(proxyModule, "proxyJSONRequest");
    const observedDelays: number[] = [];
    let elapsedSeconds = 0;

    while (elapsedSeconds <= IDEMPOTENCE_PERIOD_SECONDS) {
      queueSyncResponse(proxyMock, responseWithStatus(eventId, 208));
      await syncMetadata(db, "token");

      const state = db["db"]!.prepare(
        `SELECT retry_attempts, retry_delay_seconds
           FROM pending_events WHERE snowflake_id = ?`,
      ).get(eventId) as PendingEventRetryState;
      observedDelays.push(state.retry_delay_seconds);
      elapsedSeconds += state.retry_delay_seconds;
      expect(db.getPendingEvents()).toEqual([]);
      db["db"]!.prepare(
        "UPDATE pending_events SET next_retry_at = CURRENT_TIMESTAMP WHERE snowflake_id = ?",
      ).run(eventId);
    }

    expect(observedDelays).toEqual([
      60, 120, 240, 480, 960, 1_920, 3_840, 7_680, 14_400, 14_400, 14_400,
      14_400, 14_400,
    ]);
    expect(elapsedSeconds).toBe(87_300);

    queueSyncResponse(proxyMock, responseWithStatus(eventId, 410));
    await syncMetadata(db, "token");

    const submittedIds = proxyMock.mock.calls
      .filter(([request]) => request.path_query === "/api/v2/data")
      .map(([request]) => JSON.parse(request.body!).events[0]?.id)
      .filter((id) => id !== undefined);
    expect(submittedIds).toHaveLength(14);
    expect(new Set(submittedIds)).toEqual(new Set([eventId]));
    expect(db.getPendingEvents()).toEqual([]);
    expect(db.getSources().size).toBe(1);

    proxyMock
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: { sources: {}, items: {}, journalists: {} },
        headers: new Map(),
      })
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: { sources: {}, items: {}, journalists: {}, events: {} },
        headers: new Map(),
      });
    await syncMetadata(db, "token");

    expect(
      (
        db["db"]!.prepare("SELECT COUNT(*) AS count FROM sources").get() as {
          count: number;
        }
      ).count,
    ).toBe(0);
    expect(
      (
        db["db"]!.prepare("SELECT COUNT(*) AS count FROM items").get() as {
          count: number;
        }
      ).count,
    ).toBe(0);
  });
});
