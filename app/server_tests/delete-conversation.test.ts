import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext, createDbHelper, TestHelpers } from "./helper";
import { Crypto } from "../src/main/crypto";
import { PendingEventType } from "../src/types";

const TARGET_SOURCE = {
  uuid: "10e66c23-c687-40e2-b71c-2ce063fd50fe",
  designation: "Preservative Legislator",
};

describe.sequential("deleting source conversation", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let initialSourceCount: number;
  let initialItemCount: number;

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

    // Store initial counts
    initialSourceCount = await context.getVisibleSourceCount();
    initialItemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    console.log(`Initial source count: ${initialSourceCount}`);
    console.log(`Initial item count for target source: ${initialItemCount}`);
  }, 180000);

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("deletes conversation but keeps source account locally", async () => {
    // Verify source exists and has items before deletion
    const existsBefore = await helpers.sourceExistsInDb(TARGET_SOURCE.uuid);
    expect(existsBefore).toBe(true);
    expect(initialItemCount).toBeGreaterThan(0);

    // Select the source
    await helpers.selectSource(TARGET_SOURCE.uuid);

    // Open delete modal and delete conversation only
    await helpers.openDeleteModal();
    await helpers.clickDeleteConversation();

    // Verify source is still visible in source list
    const visibleCount = await context.getVisibleSourceCount();
    expect(visibleCount).toBe(initialSourceCount);

    // Verify pending event was created
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.SourceConversationDeleted,
    );
    expect(pendingEvents).toHaveLength(1);
    expect(pendingEvents[0].sourceUuid).toBe(TARGET_SOURCE.uuid);

    // Verify items are hidden from conversation (projected as deleted)
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(0);
  });

  it("syncs the conversation delete event with the server", async () => {
    // Run sync to push the delete event to the server
    await context.runSync();

    // Verify pending events are cleared
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.SourceConversationDeleted,
    );
    expect(pendingEvents).toHaveLength(0);

    // Verify source still exists in database
    const exists = await helpers.sourceExistsInDb(TARGET_SOURCE.uuid);
    expect(exists).toBe(true);

    // Verify all items for this source are deleted
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(0);

    // Verify source is still visible
    const visibleCount = await context.getVisibleSourceCount();
    expect(visibleCount).toBe(initialSourceCount);
  });

  it("can send new reply after conversation deletion", async () => {
    // Navigate to the source
    await helpers.navigateToSource(TARGET_SOURCE.uuid);

    // Wait for conversation to load (should be empty)
    await context.page.waitForTimeout(500);

    const uiItemCountBefore = await helpers.getConversationItemCount();

    // Send a new reply
    const replyText = "Test reply after conversation deletion";
    await helpers.sendReply(replyText);

    // Verify the reply appears in the UI
    const uiItemCountAfter = await helpers.getConversationItemCount();
    expect(uiItemCountAfter).toBe(uiItemCountBefore + 1);

    // Verify item count in DB increased
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(1);

    // Sync and verify reply persists
    await context.runSync();

    const finalItemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(finalItemCount).toBe(1);
  });
});
