import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext, createDbHelper, TestHelpers } from "./helper";
import { Crypto } from "../src/main/crypto";
import { PendingEventType } from "../src/types";

const TARGET_SOURCE = {
  uuid: "6d3a8b24-a7ec-4c8e-b646-36782b52d77e",
  designation: "Gorgeous Apron",
};

describe.sequential("deleting sources", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let initialSourceCount: number;

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

    // Store initial source count
    initialSourceCount = await context.getVisibleSourceCount();
    console.log(`Initial source count: ${initialSourceCount}`);
  }, 180000);

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("deletes a source account locally and queues an event", async () => {
    // Verify source exists before deletion
    const existsBefore = await helpers.sourceExistsInDb(TARGET_SOURCE.uuid);
    expect(existsBefore).toBe(true);

    const itemCountBefore = await helpers.getSourceItemCount(
      TARGET_SOURCE.uuid,
    );
    expect(itemCountBefore).toBe(6);

    // Select the source
    await helpers.selectSource(TARGET_SOURCE.uuid);

    // Open delete modal and delete account
    await helpers.openDeleteModal();
    await helpers.clickDeleteAccount();

    // Verify source is hidden from source list
    const visibleCount = await context.getVisibleSourceCount();
    expect(visibleCount).toBe(initialSourceCount - 1);

    // Verify pending event was created
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.SourceDeleted,
    );
    expect(pendingEvents).toHaveLength(1);
    expect(pendingEvents[0].sourceUuid).toBe(TARGET_SOURCE.uuid);
  });

  it("syncs the source delete event with the server", async () => {
    // Run sync to push the delete event to the server
    await context.runSync();

    // Verify pending events are cleared
    const pendingEvents = await helpers.getPendingEventsByType(
      PendingEventType.SourceDeleted,
    );
    expect(pendingEvents).toHaveLength(0);

    // Verify source no longer exists in database
    const exists = await helpers.sourceExistsInDb(TARGET_SOURCE.uuid);
    expect(exists).toBe(false);

    // Verify source's items also no longer exist
    const itemCount = await helpers.getSourceItemCount(TARGET_SOURCE.uuid);
    expect(itemCount).toBe(0);
  });

  it("maintains correct source count after sync", async () => {
    // Verify visible source count is still reduced
    const visibleCount = await context.getVisibleSourceCount();
    expect(visibleCount).toBe(initialSourceCount - 1);
  });
});
