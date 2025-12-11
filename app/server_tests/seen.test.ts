import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext, createDbHelper, TestHelpers } from "./helper";
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

// Items already seen by the test journalist
const ALREADY_SEEN_ITEMS = [
  "adca50a5-9f70-49db-a5ae-0c184b54c6ed", // reply, seen_by includes journalist
];

describe.sequential("conversation is seen", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let dbHelper: ReturnType<typeof createDbHelper>;

  // All items from the target source (for filtering pending events)
  const TARGET_SOURCE_ITEMS = [
    ...UNSEEN_ITEMS,
    ...ALREADY_SEEN_ITEMS,
    "cc1be744-8a71-4e52-92e7-51315b6cb643", // reply from dellsberg, seen_by: [dellsberg]
  ];

  async function getSeenPendingEventsForTargetSource(): Promise<
    Array<{ id: string; itemUuid?: string }>
  > {
    const events = await helpers.getPendingEventsByType(PendingEventType.Seen);
    return events.filter(
      (event) => event.itemUuid && TARGET_SOURCE_ITEMS.includes(event.itemUuid),
    );
  }

  async function getItemSeenBy(itemUuid: string): Promise<string[]> {
    return dbHelper.withDb(async (db) => {
      const item = db.getItem(itemUuid);
      return (item.data as ItemMetadata).seen_by;
    });
  }

  async function navigateAway(): Promise<void> {
    // Click on a different source to navigate away
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

  it("marks items as seen locally when viewing conversation", async () => {
    // Navigate to the target source conversation
    await helpers.navigateToSource(TARGET_SOURCE.uuid, true);

    // Wait for pending events to be created
    await context.page.waitForTimeout(1000);

    // Verify pending seen events were created for unseen items
    const pendingEvents = await getSeenPendingEventsForTargetSource();
    const pendingItemUuids = pendingEvents.map((e) => e.itemUuid);

    // Should have events for unseen items
    for (const itemUuid of UNSEEN_ITEMS) {
      expect(pendingItemUuids).toContain(itemUuid);
    }

    // Should NOT have events for already seen items (by this journalist)
    for (const itemUuid of ALREADY_SEEN_ITEMS) {
      expect(pendingItemUuids).not.toContain(itemUuid);
    }
  });

  it("syncs seen events with the server", async () => {
    // Run sync to push seen events to the server
    await context.runSync();

    // Verify pending seen events were cleared
    const pendingEvents = await getSeenPendingEventsForTargetSource();
    expect(pendingEvents).toHaveLength(0);

    // Verify items in DB now have the journalist's UUID in seen_by
    for (const itemUuid of UNSEEN_ITEMS) {
      const seenBy = await getItemSeenBy(itemUuid);
      expect(seenBy).toContain(JOURNALIST_UUID);
    }
  });

  it("does not duplicate seen events on revisit", async () => {
    // Navigate away from source
    await navigateAway();

    // Navigate back to the same source
    await helpers.navigateToSource(TARGET_SOURCE.uuid, true);

    // Wait for any potential pending events
    await context.page.waitForTimeout(1000);

    // Verify no new pending events are created for target source (idempotent)
    const pendingEvents = await getSeenPendingEventsForTargetSource();
    expect(pendingEvents).toHaveLength(0);
  });
});
