import fs from "fs";
import os from "os";
import path from "path";

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import {
  BatchRequest,
  BatchResponse,
  EventStatus,
  FetchStatus,
  ItemMetadata,
  PendingEventData,
  PendingEventType,
  SourceMetadata,
  SyncStatus,
} from "../../types";
import { Crypto } from "../crypto";
import { Datastore } from "../datastore";
import * as proxyModule from "../proxy";
import { Storage } from "../storage";
import { syncMetadata } from "./index";

const SOURCE_UUID = "11111111-1111-4111-8111-111111111111";
const SECOND_SOURCE_UUID = "22222222-2222-4222-8222-222222222222";
const ALIAS_UUID = "55555555-5555-4555-8555-555555555555";
const FIRST_ITEM_UUID = "aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa";
const SECOND_ITEM_UUID = "bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb";
const UNRELATED_ITEM_UUID = "cccccccc-cccc-4ccc-8ccc-cccccccccccc";
const JOURNALIST_UUID = "33333333-3333-4333-8333-333333333333";

function sourceMetadata(uuid = SOURCE_UUID): SourceMetadata {
  return {
    uuid,
    journalist_designation: "amber river",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    last_updated: "2026-07-09T00:00:00Z",
    public_key: "fake-public-key",
    fingerprint: "fake-fingerprint",
  };
}

function messageMetadata(
  uuid: string,
  interactionCount: number,
  source = SOURCE_UUID,
): ItemMetadata {
  return {
    kind: "message",
    uuid,
    source,
    size: 11,
    is_read: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

function replyMetadata(
  uuid: string,
  source = SOURCE_UUID,
  interactionCount = 3,
): ItemMetadata {
  return {
    kind: "reply",
    uuid,
    source,
    size: 15,
    journalist_uuid: JOURNALIST_UUID,
    is_deleted_by_source: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

describe("in-flight reply reconciliation", () => {
  let crypto: Crypto;
  let db: Datastore;
  let testDir: string;

  beforeEach(() => {
    vi.restoreAllMocks();
    testDir = fs.mkdtempSync(path.join(os.tmpdir(), "sd-stale-reply-"));
    (Crypto as unknown as { instance?: Crypto }).instance = undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
    vi.spyOn(crypto, "encryptSourceMessage").mockResolvedValue("ciphertext");
    db = new Datastore(crypto, new Storage(), testDir);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata() });
    db.updateItems({
      [FIRST_ITEM_UUID]: messageMetadata(FIRST_ITEM_UUID, 1),
      [SECOND_ITEM_UUID]: messageMetadata(SECOND_ITEM_UUID, 2),
    });
  });

  afterEach(() => {
    db.close();
    fs.rmSync(testDir, { recursive: true, force: true });
  });

  async function addPendingReply(
    sourceUuid = SOURCE_UUID,
    interactionCount = 3,
  ): Promise<{
    eventId: string;
    replyUuid: string;
  }> {
    const eventId = await db.addPendingReplySentEvent(
      "pending plaintext",
      sourceUuid,
      interactionCount,
    );
    const event = db.getPendingEvents().find(({ id }) => id === eventId);
    if (!event || event.type !== PendingEventType.ReplySent) {
      throw new Error("pending reply was not created");
    }
    return { eventId, replyUuid: event.data.uuid };
  }

  function mockIndexNotModified(): void {
    vi.spyOn(proxyModule, "proxyJSONRequest").mockResolvedValueOnce({
      status: 304,
      error: false,
      data: null,
      headers: new Map(),
    });
  }

  async function runDestructiveRace(
    type: PendingEventType,
    data?: PendingEventData,
  ): Promise<string> {
    const { eventId, replyUuid } = await addPendingReply();
    const response: BatchResponse = {
      events: { [eventId]: [EventStatus.OK, null] },
      items: { [replyUuid]: replyMetadata(replyUuid) },
      sources: {},
      journalists: {},
    };
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockImplementationOnce(
      async (request) => {
        const submitted = JSON.parse(request.body!) as BatchRequest;
        expect(submitted.events).toMatchObject([
          {
            id: eventId,
            type: PendingEventType.ReplySent,
            data: { uuid: replyUuid, reply: "ciphertext" },
          },
        ]);

        const destructiveEventId = db.addPendingSourceEvent(
          SOURCE_UUID,
          type,
          data,
        );
        expect(destructiveEventId).not.toBeNull();
        expect(db.getPendingEvents().map(({ id }) => id)).toEqual([
          destructiveEventId,
        ]);
        expect(db.getItem(replyUuid)).toBeNull();

        return {
          status: 200,
          error: false,
          data: response,
          headers: new Map(),
        };
      },
    );

    expect(await syncMetadata(db, "token")).toBe(SyncStatus.UPDATED);
    expect(db.getItem(replyUuid)).toBeNull();
    expect(
      db.getItemsToProcess({ messageLimit: 10, fileLimit: 10 }),
    ).not.toContain(replyUuid);
    return replyUuid;
  }

  it("discards an accepted reply after later source deletion", async () => {
    await runDestructiveRace(PendingEventType.SourceDeleted);
    expect(db.getSources()).toHaveLength(0);
  });

  it("discards an accepted reply above a later truncation bound", async () => {
    await runDestructiveRace(PendingEventType.SourceConversationTruncated, {
      upper_bound: 2,
    });
    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(0);
  });

  it("rejects an alias key for a superseded reply", async () => {
    const { eventId, replyUuid } = await addPendingReply();
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockImplementationOnce(async () => {
      db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted);
      return {
        status: 200,
        error: false,
        data: {
          events: { [eventId]: [EventStatus.OK, null] },
          items: { [ALIAS_UUID]: replyMetadata(replyUuid) },
          sources: {},
          journalists: {},
        },
        headers: new Map(),
      };
    });

    const outcome = await syncMetadata(db, "token").then(
      (status) => ({ status }),
      (error: unknown) => ({
        error: error instanceof Error ? error.message : String(error),
      }),
    );
    const alias = db.getItem(ALIAS_UUID);
    expect({
      rawAliasExists: alias !== null,
      rawAliasFetchStatus: alias?.fetch_status ?? null,
      aliasQueued: db
        .getItemsToProcess({ messageLimit: 10, fileLimit: 10 })
        .includes(ALIAS_UUID),
    }).toEqual({
      rawAliasExists: false,
      rawAliasFetchStatus: null,
      aliasQueued: false,
    });
    expect(outcome).toEqual({
      error: expect.stringContaining(
        "Item metadata UUID must match its batch map key",
      ),
    });
    expect(db.getItem(replyUuid)).toBeNull();
    expect(db.getPendingEvents()).toMatchObject([
      { type: PendingEventType.SourceDeleted },
    ]);
  });

  it("rejects an alias when batch application bypasses response parsing", async () => {
    const { eventId, replyUuid } = await addPendingReply();
    const submittedEvents = db.getPendingEvents();
    db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted);
    const response: BatchResponse = {
      events: { [eventId]: [EventStatus.OK, null] },
      items: { [ALIAS_UUID]: replyMetadata(replyUuid) },
      sources: {},
      journalists: {},
    };

    expect(() => db.updateBatch(response, submittedEvents)).toThrow(
      "Item metadata UUID must match its batch map key",
    );
    expect(db.getItem(ALIAS_UUID)).toBeNull();
    expect(db.getPendingEvents()).toMatchObject([
      { type: PendingEventType.SourceDeleted },
    ]);
  });

  it("applies reply and unrelated tombstones after supersession", async () => {
    const { eventId, replyUuid } = await addPendingReply();
    db.updateItems({ [replyUuid]: replyMetadata(replyUuid) });
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockImplementationOnce(async () => {
      db.addPendingSourceEvent(
        SOURCE_UUID,
        PendingEventType.SourceConversationTruncated,
        { upper_bound: 3 },
      );
      return {
        status: 200,
        error: false,
        data: {
          events: { [eventId]: [EventStatus.OK, null] },
          items: { [replyUuid]: null, [FIRST_ITEM_UUID]: null },
          sources: {},
          journalists: {},
        },
        headers: new Map(),
      };
    });

    expect(await syncMetadata(db, "token")).toBe(SyncStatus.UPDATED);
    expect(db.getItem(replyUuid)).toBeNull();
    expect(db.getItem(FIRST_ITEM_UUID)).toBeNull();
  });

  it("filters only superseded replies from a mixed batch", async () => {
    db.updateSources({
      [SECOND_SOURCE_UUID]: sourceMetadata(SECOND_SOURCE_UUID),
    });
    const firstReply = await addPendingReply();
    const secondReply = await addPendingReply(SECOND_SOURCE_UUID, 1);
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockImplementationOnce(async () => {
      db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted);
      return {
        status: 200,
        error: false,
        data: {
          events: {
            [firstReply.eventId]: [EventStatus.OK, null],
            [secondReply.eventId]: [EventStatus.OK, null],
          },
          items: {
            [firstReply.replyUuid]: replyMetadata(firstReply.replyUuid),
            [secondReply.replyUuid]: replyMetadata(
              secondReply.replyUuid,
              SECOND_SOURCE_UUID,
              1,
            ),
            [UNRELATED_ITEM_UUID]: messageMetadata(
              UNRELATED_ITEM_UUID,
              2,
              SECOND_SOURCE_UUID,
            ),
          },
          sources: {},
          journalists: {},
        },
        headers: new Map(),
      };
    });

    expect(await syncMetadata(db, "token")).toBe(SyncStatus.UPDATED);
    expect(db.getItem(firstReply.replyUuid)).toBeNull();
    expect(db.getItem(secondReply.replyUuid)).toMatchObject({
      plaintext: "pending plaintext",
      fetch_status: FetchStatus.Complete,
    });
    expect(db.getItem(UNRELATED_ITEM_UUID)).toMatchObject({
      fetch_status: FetchStatus.Initial,
      data: { uuid: UNRELATED_ITEM_UUID },
    });
    expect(db.getItemsToProcess({ messageLimit: 10, fileLimit: 10 })).toContain(
      UNRELATED_ITEM_UUID,
    );
    expect(db.getPendingEvents()).toMatchObject([
      { type: PendingEventType.SourceDeleted },
    ]);
  });

  it("keeps a valid in-flight reply when no later event supersedes it", async () => {
    const { eventId, replyUuid } = await addPendingReply();
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockResolvedValueOnce({
      status: 200,
      error: false,
      data: {
        events: { [eventId]: [EventStatus.OK, null] },
        items: { [replyUuid]: replyMetadata(replyUuid) },
        sources: {},
        journalists: {},
      },
      headers: new Map(),
    });

    expect(await syncMetadata(db, "token")).toBe(SyncStatus.UPDATED);
    expect(db.getPendingEvents()).toHaveLength(0);
    expect(db.getItem(replyUuid)).toMatchObject({
      uuid: replyUuid,
      plaintext: "pending plaintext",
      fetch_status: FetchStatus.Complete,
      data: replyMetadata(replyUuid),
    });
  });

  it("rolls back event reconciliation when later batch updates fail", async () => {
    const { eventId, replyUuid } = await addPendingReply();
    const versionBefore = db.getVersion();
    mockIndexNotModified();
    vi.mocked(proxyModule.proxyJSONRequest).mockResolvedValueOnce({
      status: 200,
      error: false,
      data: {
        events: { [eventId]: [EventStatus.OK, null] },
        items: {
          [replyUuid]: replyMetadata(replyUuid),
          [FIRST_ITEM_UUID]: replyMetadata(FIRST_ITEM_UUID),
        },
        sources: {},
        journalists: {},
      },
      headers: new Map(),
    });

    await expect(syncMetadata(db, "token")).rejects.toThrow(
      "items.kind is immutable",
    );
    expect(db.getVersion()).toBe(versionBefore);
    expect(db.getPendingEvents().map(({ id }) => id)).toContain(eventId);
    expect(db.getItem(replyUuid)).toBeNull();
    expect(db.getItem(FIRST_ITEM_UUID)?.data.kind).toBe("message");
  });
});
