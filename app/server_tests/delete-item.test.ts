import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext, createDbHelper, TestHelpers } from "./helper";
import { Crypto } from "../src/main/crypto";
import { PendingEventType } from "../src/types";

const TARGET_SOURCE = {
  uuid: "60a49b24-1a75-4daf-b0fa-125c1ce0d723",
  designation: "Incapable Elimination",
};

// Items to delete from this source
const ITEMS_TO_DELETE = [
  "f53f43d9-41fa-42a6-88b0-6529aaacc599", // message
  "6428c271-3108-4c73-9a44-9acfb7e2b388", // reply
];

describe.sequential("deleting items", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let initialItemCount: number;

  async function deleteItem(itemUuid: string): Promise<void> {
    // Use IPC to add pending item event since UI may not have delete button per item
    await context.page.evaluate(
      ({ uuid, eventType }) => {
        return (
          window as typeof window & {
            electronAPI: {
              addPendingItemEvent: (
                uuid: string,
                type: string,
              ) => Promise<void>;
            };
          }
        ).electronAPI.addPendingItemEvent(uuid, eventType);
      },
      { uuid: itemUuid, eventType: PendingEventType.ItemDeleted },
    );
    await context.page.waitForTimeout(500);
  }

  beforeAll(async () => {
    context = await TestContext.setup();
    const crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
    const dbHelper = createDbHelper(crypto, context.dbPath);
    helpers = new TestHelpers(context, dbHelper);
    await context.login();
    await context.runSync();

    // Store initial item count
    initialItemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    console.log(`Initial item count for source: ${initialItemCount}`);
  }, 180000);

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("deletes an item locally and queues an event", async () => {
    // Navigate to the source's conversation
    await helpers.navigateToSource(TARGET_SOURCE.uuid);

    const itemToDelete = ITEMS_TO_DELETE[0];

    // Delete the item
    await deleteItem(itemToDelete);

    // Verify a pending event was created
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.ItemDeleted,
    );
    expect(pendingEvents).toHaveLength(1);
    expect(pendingEvents[0].itemUuid).toBe(itemToDelete);

    // Verify the item count decreased (item is hidden/projected as deleted)
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(initialItemCount - 1);
  });

  it("syncs the delete event with the server", async () => {
    // Run sync to push the delete event to the server
    await context.runSync();

    // Verify the pending event was cleared
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.ItemDeleted,
    );
    expect(pendingEvents).toHaveLength(0);

    // Verify the item no longer exists in the database
    const exists = await helpers.itemExistsInDb(ITEMS_TO_DELETE[0]);
    expect(exists).toBe(false);

    // Verify item count is still reduced
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(initialItemCount - 1);
  });

  it("can delete multiple items before sync", async () => {
    // Ensure we're on the source conversation
    await helpers.navigateToSource(TARGET_SOURCE.uuid);

    const itemCountBefore = await helpers.getSourceItemCount(
      TARGET_SOURCE.uuid,
    );

    // Delete remaining item
    const itemToDelete = ITEMS_TO_DELETE[1];
    await deleteItem(itemToDelete);

    // Verify pending event was created
    let pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.ItemDeleted,
    );
    expect(pendingEvents).toHaveLength(1);

    // Verify item count decreased
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(itemCountBefore - 1);

    // Sync and verify event is processed
    await context.runSync();

    pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.ItemDeleted,
    );
    expect(pendingEvents).toHaveLength(0);

    // Verify item no longer exists
    const exists = await helpers.itemExistsInDb(itemToDelete);
    expect(exists).toBe(false);
  });
});
