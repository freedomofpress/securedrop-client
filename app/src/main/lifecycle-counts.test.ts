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
  vi,
} from "vitest";

import {
  BatchResponseSchema,
  PendingEventSchema,
  PendingEventType,
} from "../schemas";
import {
  EventStatus,
  FetchStatus,
  ItemMetadata,
  SourceMetadata,
} from "../types";
import { Crypto } from "./crypto";
import { Datastore } from "./datastore";
import * as proxyModule from "./proxy";
import { Storage } from "./storage";
import { syncMetadata } from "./sync";

const SOURCE_UUID = "11111111-1111-4111-8111-111111111111";
const SECOND_SOURCE_UUID = "22222222-2222-4222-8222-222222222222";
const ITEM_UUID = "33333333-3333-4333-8333-333333333333";
const SECOND_ITEM_UUID = "44444444-4444-4444-8444-444444444444";
const THIRD_ITEM_UUID = "66666666-6666-4666-8666-666666666666";
const FOURTH_ITEM_UUID = "77777777-7777-4777-8777-777777777777";
const FIFTH_ITEM_UUID = "88888888-8888-4888-8888-888888888888";
const JOURNALIST_UUID = "55555555-5555-4555-8555-555555555555";

const BOUNDARY_CASES = [
  {
    label: "below the safe integer minimum",
    value: Number.MIN_SAFE_INTEGER - 1,
    itemValid: false,
    eventValid: false,
  },
  {
    label: "safe integer minimum",
    value: Number.MIN_SAFE_INTEGER,
    itemValid: false,
    eventValid: false,
  },
  { label: "negative integer", value: -1, itemValid: false, eventValid: false },
  {
    label: "negative fraction",
    value: -0.5,
    itemValid: false,
    eventValid: false,
  },
  { label: "zero", value: 0, itemValid: false, eventValid: true },
  {
    label: "smallest positive fraction",
    value: Number.MIN_VALUE,
    itemValid: false,
    eventValid: false,
  },
  {
    label: "positive fraction below one",
    value: 0.5,
    itemValid: false,
    eventValid: false,
  },
  { label: "one", value: 1, itemValid: true, eventValid: true },
  {
    label: "positive fraction above one",
    value: 1.5,
    itemValid: false,
    eventValid: false,
  },
  {
    label: "below the safe integer maximum",
    value: Number.MAX_SAFE_INTEGER - 1,
    itemValid: true,
    eventValid: true,
  },
  {
    label: "safe integer maximum",
    value: Number.MAX_SAFE_INTEGER,
    itemValid: true,
    eventValid: true,
  },
  {
    label: "above the safe integer maximum",
    value: Number.MAX_SAFE_INTEGER + 1,
    itemValid: false,
    eventValid: false,
  },
  { label: "NaN", value: Number.NaN, itemValid: false, eventValid: false },
  {
    label: "positive infinity",
    value: Number.POSITIVE_INFINITY,
    itemValid: false,
    eventValid: false,
  },
  {
    label: "negative infinity",
    value: Number.NEGATIVE_INFINITY,
    itemValid: false,
    eventValid: false,
  },
];

function batchResponse(kind: "message" | "reply", interactionCount: number) {
  const metadata =
    kind === "reply"
      ? {
          kind,
          uuid: ITEM_UUID,
          source: SOURCE_UUID,
          size: 22,
          journalist_uuid: JOURNALIST_UUID,
          is_deleted_by_source: false,
          seen_by: [],
          interaction_count: interactionCount,
        }
      : {
          kind,
          uuid: ITEM_UUID,
          source: SOURCE_UUID,
          size: 22,
          is_read: false,
          seen_by: [],
          interaction_count: interactionCount,
        };
  return {
    sources: {},
    items: { [ITEM_UUID]: metadata },
    journalists: {},
    events: {},
  };
}

function pendingEvent(type: PendingEventType, upperBound: number) {
  return {
    id: "123",
    type,
    target: { source_uuid: SOURCE_UUID, version: "source-version" },
    data: { upper_bound: upperBound },
  };
}

describe.each([
  {
    domain: "message interaction_count",
    expected: "itemValid" as const,
    value: (count: number) => batchResponse("message", count),
  },
  {
    domain: "reply interaction_count",
    expected: "itemValid" as const,
    value: (count: number) => batchResponse("reply", count),
  },
  {
    domain: "seen upper_bound",
    expected: "eventValid" as const,
    value: (count: number) =>
      pendingEvent(PendingEventType.SourceConversationSeen, count),
  },
  {
    domain: "truncation upper_bound",
    expected: "eventValid" as const,
    value: (count: number) =>
      pendingEvent(PendingEventType.SourceConversationTruncated, count),
  },
])("$domain boundary matrix", ({ expected, value }) => {
  it.each(BOUNDARY_CASES)("handles $label", (boundary) => {
    const schema =
      expected === "itemValid" ? BatchResponseSchema : PendingEventSchema;
    expect(schema.safeParse(value(boundary.value)).success).toBe(
      boundary[expected],
    );
  });
});

it("leaves duplicate positive interaction counts for global validation", () => {
  const singleItemBatch = batchResponse("message", 1);
  const batch = {
    ...singleItemBatch,
    items: {
      ...singleItemBatch.items,
      [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 1),
    },
  };

  expect(BatchResponseSchema.safeParse(batch).success).toBe(true);
});

it("rejects an item whose metadata UUID differs from its map key", () => {
  const validBatch = batchResponse("message", 1);
  const mismatchedBatch = {
    ...validBatch,
    items: {
      [SECOND_ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
    },
  };

  expect(BatchResponseSchema.safeParse(mismatchedBatch).success).toBe(false);
});

describe.each([
  PendingEventType.SourceConversationSeen,
  PendingEventType.SourceConversationTruncated,
])("PendingEventSchema %s upper_bound", (type) => {
  it("rejects missing data", () => {
    expect(
      PendingEventSchema.safeParse({
        id: "123",
        type,
        target: { source_uuid: SOURCE_UUID, version: "source-version" },
      }).success,
    ).toBe(false);
  });
});

function sourceMetadata(uuid: string): SourceMetadata {
  return {
    uuid,
    journalist_designation: "able baker",
    is_starred: false,
    is_seen: false,
    has_attachment: false,
    last_updated: "2026-07-10T00:00:00Z",
    public_key: "fake-public-key",
    fingerprint: "fake-fingerprint",
  };
}

function itemMetadata(
  uuid: string,
  sourceUuid: string,
  interactionCount: number,
): ItemMetadata {
  return {
    kind: "message",
    uuid,
    source: sourceUuid,
    size: 22,
    is_read: false,
    seen_by: [],
    interaction_count: interactionCount,
  };
}

describe("lifecycle count datastore boundaries", () => {
  const originalHomedir = os.homedir;
  let crypto: Crypto;
  let db: Datastore;
  let storage: Storage;
  let tmpDir: string;

  beforeAll(() => {
    (Crypto as unknown as { instance: Crypto | undefined }).instance =
      undefined;
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  });

  beforeEach(() => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "sd-lifecycle-counts-"));
    os.homedir = () => tmpDir;
    storage = new Storage();
    db = new Datastore(crypto, storage, tmpDir);
  });

  afterEach(() => {
    vi.restoreAllMocks();
    db.close();
    os.homedir = originalHomedir;
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });

  it("rejects an invalid sync batch before applying planned deletions", async () => {
    const existingItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: existingItem });
    db.completePlaintextItem(ITEM_UUID, "existing searchable secret");
    const itemDirectory = storage.itemDirectory(existingItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "secret");

    const clientIndex = db.getIndex();
    const batch = {
      sources: {},
      items: {
        [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 1.5),
      },
      journalists: {},
      events: {},
    };
    vi.spyOn(proxyModule, "proxyJSONRequest")
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: {
          sources: clientIndex.sources,
          items: { [SECOND_ITEM_UUID]: "second-item-version" },
          journalists: {},
        },
        headers: new Map(),
      })
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: batch,
        headers: new Map(),
      });

    await expect(syncMetadata(db, "token")).rejects.toThrow();

    expect(db.getItem(ITEM_UUID)).not.toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)).toBeNull();
    expect(db.search("existing searchable")).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(true);
  });

  it("rejects zero and negative cursors through the real sync path", async () => {
    const existingItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: existingItem });
    db.completePlaintextItem(ITEM_UUID, "zero cursor rollback secret");
    const itemDirectory = storage.itemDirectory(existingItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "secret");

    const clientIndex = db.getIndex();
    vi.spyOn(proxyModule, "proxyJSONRequest")
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: {
          sources: clientIndex.sources,
          items: {
            [SECOND_ITEM_UUID]: "zero-item-version",
            [THIRD_ITEM_UUID]: "negative-item-version",
          },
          journalists: {},
        },
        headers: new Map(),
      })
      .mockResolvedValueOnce({
        status: 200,
        error: false,
        data: {
          sources: {},
          items: {
            [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 0),
            [THIRD_ITEM_UUID]: itemMetadata(THIRD_ITEM_UUID, SOURCE_UUID, -1),
          },
          journalists: {},
          events: {},
        },
        headers: new Map(),
      });

    await expect(syncMetadata(db, "token")).rejects.toThrow();

    expect(db.getItem(ITEM_UUID)).not.toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)).toBeNull();
    expect(db.getItem(THIRD_ITEM_UUID)).toBeNull();
    expect(db.search("zero cursor rollback")).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(true);
  });

  it("rolls back planned deletions when the batch transaction fails", () => {
    const deletedItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    const updatedItem = itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 2);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({
      [ITEM_UUID]: deletedItem,
      [SECOND_ITEM_UUID]: updatedItem,
    });
    db.completePlaintextItem(ITEM_UUID, "rollback searchable secret");
    const itemDirectory = storage.itemDirectory(deletedItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "secret");

    expect(() =>
      db.updateBatch(
        {
          sources: {},
          items: {
            [SECOND_ITEM_UUID]: {
              kind: "file",
              uuid: SECOND_ITEM_UUID,
              source: SOURCE_UUID,
              size: 22,
              is_read: false,
              seen_by: [],
              interaction_count: 2,
            },
          },
          journalists: {},
          events: {},
        },
        { sources: [], items: [ITEM_UUID], journalists: [] },
      ),
    ).toThrow("items.kind is immutable");

    expect(db.getItem(ITEM_UUID)).not.toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)?.data.kind).toBe("message");
    expect(db.search("rollback searchable")).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(true);
  });

  it("rolls back direct item writes when one interaction count is invalid", () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });

    expect(() =>
      db.updateItems({
        [ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
        [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 1.5),
      }),
    ).toThrow();

    expect(db.getItem(ITEM_UUID)).toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)).toBeNull();
  });

  it("rolls back source event batches when one upper bound is invalid", () => {
    db.updateSources({
      [SOURCE_UUID]: sourceMetadata(SOURCE_UUID),
      [SECOND_SOURCE_UUID]: sourceMetadata(SECOND_SOURCE_UUID),
    });
    db.updateItems({
      [ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
      [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SECOND_SOURCE_UUID, 1),
    });

    expect(() =>
      db.addPendingSourceEventBatch([
        {
          sourceUuid: SOURCE_UUID,
          type: PendingEventType.SourceConversationTruncated,
          data: { upper_bound: 1 },
        },
        {
          sourceUuid: SECOND_SOURCE_UUID,
          type: PendingEventType.SourceConversationTruncated,
          data: { upper_bound: 1.5 },
        },
      ]),
    ).toThrow();

    expect(db.getPendingEvents()).toHaveLength(0);
    expect(db.getItem(ITEM_UUID)?.fetch_status).toBe(FetchStatus.Initial);
    expect(db.getItem(SECOND_ITEM_UUID)?.fetch_status).toBe(
      FetchStatus.Initial,
    );
    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(1);
    expect(db.getSourceWithItems(SECOND_SOURCE_UUID).items).toHaveLength(1);
  });

  it("rejects unexpected source event data before mutation", () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });

    expect(() =>
      db.addPendingSourceEvent(SOURCE_UUID, PendingEventType.SourceDeleted, {
        upper_bound: 1,
      }),
    ).toThrow();

    expect(db.getPendingEvents()).toHaveLength(0);
    expect(db.getSourceWithItems(SOURCE_UUID).uuid).toBe(SOURCE_UUID);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
  });

  it("accepts zero seen bounds but rejects invalid item counts", async () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({
      [ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
    });

    expect(() =>
      db.addPendingSourceConversationSeen(SOURCE_UUID, Number.NaN),
    ).toThrow();
    expect(db.addPendingSourceConversationSeen(SOURCE_UUID, 0)).toBeNull();
    await expect(
      db.addPendingReplySentEvent("reply", SOURCE_UUID, 1.5),
    ).rejects.toThrow();

    expect(db.getPendingEvents()).toHaveLength(0);
    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(1);
  });

  it("cleans pre-existing invalid lifecycle state on startup", async () => {
    const fractionalItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 1.5);
    const zeroItem: ItemMetadata = {
      kind: "file",
      uuid: SECOND_ITEM_UUID,
      source: SOURCE_UUID,
      size: 22,
      is_read: false,
      seen_by: [],
      interaction_count: 0,
    };
    const validItem = itemMetadata(
      THIRD_ITEM_UUID,
      SOURCE_UUID,
      Number.MAX_SAFE_INTEGER,
    );
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [THIRD_ITEM_UUID]: validItem });
    db.completePlaintextItem(THIRD_ITEM_UUID, "valid maximum secret");
    const zeroEventId = db.addPendingSourceEvent(
      SOURCE_UUID,
      PendingEventType.SourceConversationTruncated,
      { upper_bound: 0 },
    );
    const validEventId = db.addPendingSourceEvent(
      SOURCE_UUID,
      PendingEventType.Starred,
    );
    const replyEventId = "fractional-reply";
    const rawDb = db["db"]!;
    rawDb
      .prepare(
        `INSERT INTO items (uuid, data, plaintext, version, fetch_status)
         VALUES (?, ?, ?, ?, ?)`,
      )
      .run(
        ITEM_UUID,
        JSON.stringify(fractionalItem),
        "pre-existing fractional secret",
        "fractional-version",
        FetchStatus.Complete,
      );
    rawDb
      .prepare(
        `INSERT INTO items (uuid, data, plaintext, version, fetch_status)
         VALUES (?, ?, ?, ?, ?)`,
      )
      .run(
        SECOND_ITEM_UUID,
        JSON.stringify(zeroItem),
        "pre-existing zero secret",
        "zero-version",
        FetchStatus.Complete,
      );
    rawDb
      .prepare(
        `INSERT INTO search_index(source_uuid, item_uuid, type, content)
         VALUES (?, ?, 'message', ?)`,
      )
      .run(SOURCE_UUID, ITEM_UUID, "pre-existing fractional secret");
    rawDb
      .prepare(
        `INSERT INTO search_index(source_uuid, item_uuid, type, content)
         VALUES (?, ?, 'message', ?)`,
      )
      .run(SOURCE_UUID, SECOND_ITEM_UUID, "pre-existing zero secret");
    rawDb
      .prepare(
        `INSERT INTO pending_events (snowflake_id, source_uuid, type, data)
         VALUES (?, ?, ?, ?)`,
      )
      .run(
        "fractional-truncation",
        SOURCE_UUID,
        PendingEventType.SourceConversationTruncated,
        JSON.stringify({ upper_bound: 1.5 }),
      );
    rawDb
      .prepare(
        `INSERT INTO pending_events (snowflake_id, source_uuid, type, data)
         VALUES (?, ?, ?, ?)`,
      )
      .run(
        replyEventId,
        SOURCE_UUID,
        PendingEventType.ReplySent,
        JSON.stringify({
          uuid: FOURTH_ITEM_UUID,
          metadata: {
            kind: "reply",
            uuid: FOURTH_ITEM_UUID,
            source: SOURCE_UUID,
            size: 27,
            journalist_uuid: "",
            is_deleted_by_source: false,
            seen_by: [],
            interaction_count: 1.5,
          },
          plaintext: "unsent journalist plaintext",
          reply: "encrypted reply payload",
        }),
      );
    const itemDirectory = storage.itemDirectory(fractionalItem).path;
    const zeroItemDirectory = storage.itemDirectory(zeroItem).path;
    const validItemDirectory = storage.itemDirectory(validItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "secret");
    fs.writeFileSync(path.join(zeroItemDirectory, "plaintext"), "secret");
    fs.writeFileSync(path.join(validItemDirectory, "plaintext"), "secret");

    expect(db.search("pre-existing fractional")).toHaveLength(1);
    expect(
      rawDb
        .prepare(
          "SELECT COUNT(*) AS count FROM search_index WHERE item_uuid = ?",
        )
        .get(SECOND_ITEM_UUID),
    ).toEqual({ count: 1 });
    expect(db.search("valid maximum")).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(true);
    expect(fs.existsSync(zeroItemDirectory)).toBe(true);
    expect(fs.existsSync(validItemDirectory)).toBe(true);

    await db.cleanupInvalidLifecycleData();

    expect(db.getItem(ITEM_UUID)).toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)).toBeNull();
    expect(db.getItem(THIRD_ITEM_UUID)).not.toBeNull();
    expect(db.search("pre-existing fractional")).toHaveLength(0);
    expect(
      rawDb
        .prepare(
          "SELECT COUNT(*) AS count FROM search_index WHERE item_uuid = ?",
        )
        .get(SECOND_ITEM_UUID),
    ).toEqual({ count: 0 });
    expect(db.search("valid maximum")).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(false);
    expect(fs.existsSync(zeroItemDirectory)).toBe(false);
    expect(fs.existsSync(validItemDirectory)).toBe(true);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
    const remainingEvents = db.getPendingEvents();
    expect(remainingEvents.map(({ id }) => id)).toEqual(
      expect.arrayContaining([zeroEventId, validEventId, replyEventId]),
    );
    expect(remainingEvents).toHaveLength(3);
    expect(remainingEvents.find(({ id }) => id === replyEventId)?.data).toEqual(
      expect.objectContaining({
        plaintext: "unsent journalist plaintext",
        reply: "encrypted reply payload",
        metadata: expect.objectContaining({
          interaction_count: Number.MAX_SAFE_INTEGER,
        }),
      }),
    );
  });

  it("discards a malformed legacy truncation without deleting valid data", async () => {
    const validItem = itemMetadata(FIFTH_ITEM_UUID, SOURCE_UUID, 1);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [FIFTH_ITEM_UUID]: validItem });
    const itemDirectory = storage.itemDirectory(validItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "valid secret");
    db["db"]!.prepare(
      `INSERT INTO pending_events (snowflake_id, source_uuid, type, data)
       VALUES (?, ?, ?, ?)`,
    ).run(
      "fractional-truncation",
      SOURCE_UUID,
      PendingEventType.SourceConversationTruncated,
      JSON.stringify({ upper_bound: 1.5 }),
    );

    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(0);
    await db.cleanupInvalidLifecycleData();

    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(1);
    expect(fs.existsSync(itemDirectory)).toBe(true);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
  });

  it("quarantines an aliased legacy item without deleting a shared path", async () => {
    const victimItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    const aliasedMetadata = itemMetadata(ITEM_UUID, SOURCE_UUID, 1.5);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: victimItem });
    db.completePlaintextItem(ITEM_UUID, "valid victim secret");
    const victimDirectory = storage.itemDirectory(victimItem).path;
    const rowIdentityDirectory = storage.itemDirectoryByIdentity(
      SOURCE_UUID,
      SECOND_ITEM_UUID,
      true,
    ).path;
    fs.writeFileSync(path.join(victimDirectory, "plaintext"), "victim");
    const historicalAliasFile = path.join(victimDirectory, "alias-ciphertext");
    const rowIdentityFile = path.join(rowIdentityDirectory, "row-ciphertext");
    fs.writeFileSync(historicalAliasFile, "alias");
    fs.writeFileSync(rowIdentityFile, "row");
    const rawDb = db["db"]!;
    rawDb
      .prepare(
        `INSERT INTO items (uuid, data, plaintext, version, fetch_status)
         VALUES (?, ?, ?, ?, ?)`,
      )
      .run(
        SECOND_ITEM_UUID,
        JSON.stringify(aliasedMetadata),
        "invalid alias secret",
        "alias-version",
        FetchStatus.Complete,
      );
    rawDb
      .prepare(
        `INSERT INTO search_index(source_uuid, item_uuid, type, content)
         VALUES (?, ?, 'message', ?)`,
      )
      .run(SOURCE_UUID, SECOND_ITEM_UUID, "invalid alias secret");
    await db.cleanupInvalidLifecycleData();

    expect(db.getItem(ITEM_UUID)).not.toBeNull();
    expect(db.getItem(SECOND_ITEM_UUID)).toBeNull();
    expect(db.search("valid victim")).toHaveLength(1);
    expect(db.search("invalid alias")).toHaveLength(0);
    expect(fs.existsSync(victimDirectory)).toBe(true);
    expect(fs.readFileSync(historicalAliasFile, "utf8")).toBe("alias");
    expect(fs.readFileSync(rowIdentityFile, "utf8")).toBe("row");
    expect(db.getFilesystemCleanupJobs()).toEqual([
      expect.objectContaining({
        target: "item",
        source_uuid: SOURCE_UUID,
        item_uuid: SECOND_ITEM_UUID,
        metadata_item_uuid: ITEM_UUID,
        status: "quarantined",
        reason: "metadata_uuid_mismatch",
      }),
    ]);
  });

  it("does not give a projected reply alias filesystem identity", () => {
    const victimItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 2);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: victimItem });
    const victimDirectory = storage.itemDirectory(victimItem).path;
    fs.writeFileSync(path.join(victimDirectory, "plaintext"), "victim");
    db["db"]!.prepare(
      `INSERT INTO pending_events (snowflake_id, source_uuid, type, data)
         VALUES (?, ?, ?, ?)`,
    ).run(
      "reply-alias",
      SOURCE_UUID,
      PendingEventType.ReplySent,
      JSON.stringify({
        uuid: ITEM_UUID,
        metadata: {
          kind: "reply",
          uuid: ITEM_UUID,
          source: SOURCE_UUID,
          size: 5,
          journalist_uuid: "",
          is_deleted_by_source: false,
          seen_by: [],
          interaction_count: 1,
        },
        plaintext: "alias",
        reply: "encrypted reply payload",
      }),
    );

    const projectedAlias = db
      .getSourceWithItems(SOURCE_UUID)
      .items.find(({ plaintext }) => plaintext === "alias");

    expect(projectedAlias).toBeDefined();
    expect(projectedAlias?.source_uuid).toBeUndefined();
    expect(fs.existsSync(victimDirectory)).toBe(true);
  });

  it("retries a failed cleanup job after restart", async () => {
    const zeroItem = itemMetadata(ITEM_UUID, SOURCE_UUID, 0);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    const rawDb = db["db"]!;
    rawDb
      .prepare(
        `INSERT INTO items (uuid, data, plaintext, version, fetch_status)
         VALUES (?, ?, ?, ?, ?)`,
      )
      .run(
        ITEM_UUID,
        JSON.stringify(zeroItem),
        "retryable cleanup secret",
        "zero-version",
        FetchStatus.Complete,
      );
    rawDb
      .prepare(
        `INSERT INTO search_index(source_uuid, item_uuid, type, content)
         VALUES (?, ?, 'message', ?)`,
      )
      .run(SOURCE_UUID, ITEM_UUID, "retryable cleanup secret");
    const itemDirectory = storage.itemDirectory(zeroItem).path;
    fs.writeFileSync(path.join(itemDirectory, "plaintext"), "secret");
    vi.spyOn(console, "error").mockImplementation(() => undefined);
    vi.spyOn(fs.promises, "rm").mockRejectedValue(
      new Error("permission denied"),
    );

    await db.cleanupInvalidLifecycleData();

    expect(db.getItem(ITEM_UUID)).toBeNull();
    expect(db.search("retryable cleanup")).toHaveLength(0);
    expect(fs.existsSync(itemDirectory)).toBe(true);
    expect(db.getFilesystemCleanupJobs()).toEqual([
      expect.objectContaining({
        item_uuid: ITEM_UUID,
        status: "pending",
      }),
    ]);
    expect(() =>
      db.updateItems({
        [ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
      }),
    ).toThrow("before pending filesystem cleanup completes");

    vi.mocked(fs.promises.rm).mockRestore();
    db.close();
    db = new Datastore(crypto, storage, tmpDir);
    await db.cleanupInvalidLifecycleData();

    expect(db.getItem(ITEM_UUID)).toBeNull();
    expect(db.search("retryable cleanup")).toHaveLength(0);
    expect(fs.existsSync(itemDirectory)).toBe(false);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
  });

  it("rolls back event mutation when cleanup job insertion fails", () => {
    const item = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: item });
    const itemDirectory = storage.itemDirectory(item).path;
    const plaintext = path.join(itemDirectory, "plaintext");
    fs.writeFileSync(plaintext, "secret");
    const rawDb = db["db"]!;
    rawDb.exec(`
      CREATE TRIGGER fail_cleanup_job_insert
      BEFORE INSERT ON filesystem_cleanup_jobs
      BEGIN
        SELECT RAISE(ABORT, 'injected cleanup insertion failure');
      END;
    `);

    expect(() =>
      db.addPendingSourceEvent(
        SOURCE_UUID,
        PendingEventType.SourceConversationTruncated,
        { upper_bound: 1 },
      ),
    ).toThrow("injected cleanup insertion failure");

    expect(db.getPendingEvents()).toHaveLength(0);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
    expect(db.getItem(ITEM_UUID)?.fetch_status).toBe(FetchStatus.Initial);
    expect(fs.readFileSync(plaintext, "utf8")).toBe("secret");
  });

  it("retains an acknowledged truncation cleanup across restart", async () => {
    const item = itemMetadata(ITEM_UUID, SOURCE_UUID, 1);
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({ [ITEM_UUID]: item });
    const itemDirectory = storage.itemDirectory(item).path;
    const plaintext = path.join(itemDirectory, "plaintext");
    fs.writeFileSync(plaintext, "orphan prevention secret");
    vi.spyOn(console, "error").mockImplementation(() => undefined);
    vi.spyOn(fs.promises, "rm").mockRejectedValue(
      new Error("persistent permission failure"),
    );
    const eventId = db.addPendingSourceEvent(
      SOURCE_UUID,
      PendingEventType.SourceConversationTruncated,
      { upper_bound: 1 },
    )!;
    await db.runFilesystemCleanupJobs();

    db.updateBatch(
      {
        sources: {},
        items: {},
        journalists: {},
        events: { [eventId]: [EventStatus.OK, null] },
      },
      { sources: [], items: [ITEM_UUID], journalists: [] },
    );
    await db.runFilesystemCleanupJobs();

    expect(db.getItem(ITEM_UUID)).toBeNull();
    expect(db.getPendingEvents()).toHaveLength(0);
    expect(fs.readFileSync(plaintext, "utf8")).toBe("orphan prevention secret");
    expect(db.getFilesystemCleanupJobs()).toEqual([
      expect.objectContaining({ item_uuid: ITEM_UUID, status: "pending" }),
    ]);

    vi.mocked(fs.promises.rm).mockRestore();
    db.close();
    db = new Datastore(crypto, storage, tmpDir);
    await db.cleanupInvalidLifecycleData();

    expect(fs.existsSync(plaintext)).toBe(false);
    expect(db.getFilesystemCleanupJobs()).toHaveLength(0);
  });

  it("preserves coherent zero-bound truncation behavior", () => {
    db.updateSources({ [SOURCE_UUID]: sourceMetadata(SOURCE_UUID) });
    db.updateItems({
      [ITEM_UUID]: itemMetadata(ITEM_UUID, SOURCE_UUID, 1),
      [SECOND_ITEM_UUID]: itemMetadata(SECOND_ITEM_UUID, SOURCE_UUID, 2),
    });
    db.completePlaintextItem(ITEM_UUID, "zero-bound secret");
    db.completePlaintextItem(SECOND_ITEM_UUID, "positive-count secret");

    const eventId = db.addPendingSourceEvent(
      SOURCE_UUID,
      PendingEventType.SourceConversationTruncated,
      { upper_bound: 0 },
    );

    expect(eventId).not.toBeNull();
    expect(db.getPendingEvents()).toEqual([
      expect.objectContaining({
        id: eventId,
        type: PendingEventType.SourceConversationTruncated,
        data: { upper_bound: 0 },
      }),
    ]);
    expect(db.getItem(ITEM_UUID)?.fetch_status).toBe(FetchStatus.Complete);
    expect(db.getItem(SECOND_ITEM_UUID)?.fetch_status).toBe(
      FetchStatus.Complete,
    );
    expect(db.getSourceWithItems(SOURCE_UUID).items).toHaveLength(2);
    expect(db.search("zero-bound")).toHaveLength(1);
    expect(db.search("positive-count")).toHaveLength(1);
  });
});
