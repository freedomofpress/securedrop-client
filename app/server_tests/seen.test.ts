import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext, createDbHelper, TestHelpers, pollUntil } from "./helper";
import { Crypto } from "../src/main/crypto";
import { PendingEventType, ItemMetadata } from "../src/types";

const TARGET_SOURCE = {
  uuid: "10e66c23-c687-40e2-b71c-2ce063fd50fe",
  designation: "Preservative Legislator",
};

const JOURNALIST_UUID = "be726875-1290-49d4-922d-2fc0901c9266";

// Items in this source that are NOT seen by the test journalist
const UNSEEN_ITEMS = [
  "b8260d37-87b2-49b3-a235-bac31c11021d", // message, seen_by: []
  "85f0d337-b077-41b6-a914-33fee7bfcaa1", // file, seen_by: []
  "31eeac69-e02f-46f1-a5da-b8f912eb773d", // file, seen_by: []
  "96325861-741a-41eb-91b5-bb1ff34f3e70", // message, seen_by: []
];

describe.sequential("conversation is seen", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let dbHelper: ReturnType<typeof createDbHelper>;

  async function getConversationSeenEventForTargetSource(): Promise<
    Array<{ id: string; sourceUuid?: string }>
  > {
    const events = await helpers.getPendingEventsByType(
      PendingEventType.SourceConversationSeen,
    );
    return events.filter((event) => event.sourceUuid === TARGET_SOURCE.uuid);
  }

  async function getItemSeenBy(itemUuid: string): Promise<string[]> {
    return dbHelper.withDb(async (db) => {
      const item = db.getItem(itemUuid)!;
      return (item.data as ItemMetadata).seen_by;
    });
  }

  async function navigateAway(): Promise<void> {
    const otherSource = "60a49b24-1a75-4daf-b0fa-125c1ce0d723";
    await helpers.navigateToSource(otherSource);
  }

  beforeAll(async () => {
    context = await TestContext.setup();
    const crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
    dbHelper = createDbHelper(crypto, context.dbPath);
    helpers = new TestHelpers(context, dbHelper);
    await context.login();
    await context.runSync();
  }, 180000);

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("creates a SourceConversationSeen pending event when viewing conversation", async () => {
    await helpers.navigateToSource(TARGET_SOURCE.uuid);

    await pollUntil(
      () => getConversationSeenEventForTargetSource(),
      (events) => events.length === 1,
      5000,
    );

    const pendingEvents = await getConversationSeenEventForTargetSource();
    expect(pendingEvents).toHaveLength(1);
  });

  it("syncs SourceConversationSeen event with the server", async () => {
    await context.runSync();

    // Verify pending event was cleared after sync
    const pendingEvents = await getConversationSeenEventForTargetSource();
    expect(pendingEvents).toHaveLength(0);

    // Verify items in DB now have the journalist's UUID in seen_by
    for (const itemUuid of UNSEEN_ITEMS) {
      const seenBy = await getItemSeenBy(itemUuid);
      expect(seenBy).toContain(JOURNALIST_UUID);
    }
  });

  it("does not duplicate SourceConversationSeen event on revisit", async () => {
    await navigateAway();
    await helpers.navigateToSource(TARGET_SOURCE.uuid);
    await context.page.waitForTimeout(500);

    // After sync already cleared items, revisiting should create no new event
    // (all items now have is_read=true from server, so upper_bound is already covered)
    const pendingEvents = await getConversationSeenEventForTargetSource();
    expect(pendingEvents).toHaveLength(0);
  });
});
