import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext } from "./helper";
import { DB } from "../src/main/database";
import { Crypto } from "../src/main/crypto";
import { PendingEventType, ReplySentData } from "../src/types";

const TARGET_SOURCE = {
  uuid: "60a49b24-1a75-4daf-b0fa-125c1ce0d723",
  designation: "Incapable Elimination",
};

describe.sequential("sending replies", () => {
  let context: TestContext;
  let crypto: Crypto;
  let initialItemCount: number;

  function withDb<T>(callback: (db: DB) => Promise<T> | T): Promise<T> {
    const db = new DB(crypto, context.dbPath);
    return Promise.resolve(callback(db)).finally(() => db.close());
  }

  async function getReplyPendingEvents(): Promise<
    Array<{
      id: string;
      type: PendingEventType;
      data: ReplySentData;
    }>
  > {
    return withDb(async (db) => {
      return db
        .getPendingEvents()
        .filter((event) => event.type === PendingEventType.ReplySent)
        .filter((event) => {
          if ("source_uuid" in event.target) {
            return event.target.source_uuid === TARGET_SOURCE.uuid;
          }
          return false;
        })
        .map((event) => ({
          id: event.id,
          type: event.type,
          data: event.data as ReplySentData,
        }));
    });
  }

  async function getItemCount(): Promise<number> {
    return withDb(async (db) => {
      const sourceWithItems = db.getSourceWithItems(TARGET_SOURCE.uuid);
      return sourceWithItems.items.length;
    });
  }

  async function getConversationItemCount(): Promise<number> {
    const items = context.page.locator('[data-testid^="item-"]');
    return await items.count();
  }

  async function navigateToSource(): Promise<void> {
    // Check if the conversation is already visible (source might already be selected)
    const conversationContainer = context.page.getByTestId(
      "conversation-items-container",
    );
    const isAlreadyVisible = await conversationContainer
      .isVisible()
      .catch(() => false);

    if (!isAlreadyVisible) {
      // Click to select the source
      await context.page.getByTestId(`source-${TARGET_SOURCE.uuid}`).click();
      await context.page.waitForTimeout(500);
      // Wait for conversation to load
      await expect(conversationContainer).toBeVisible({ timeout: 5000 });
    }
  }

  async function sendReply(message: string): Promise<void> {
    await context.page.getByTestId("reply-textarea").fill(message);
    await context.page.getByTestId("send-button").click();
    await context.page.waitForTimeout(500);
  }

  beforeAll(async () => {
    context = await TestContext.setup();
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
    await context.login();
    await context.runSync();

    // Store initial item count
    initialItemCount = await getItemCount();
    console.log(`Initial item count for source: ${initialItemCount}`);
  }, 180000); // 3 minutes for server startup + login

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("sends a reply locally and queues an event", async () => {
    // Navigate to the source's conversation
    await navigateToSource();

    const uiItemCountBefore = await getConversationItemCount();
    console.log(`UI item count before reply: ${uiItemCountBefore}`);

    // Send a reply
    const replyText = "Test reply from e2e test";
    await sendReply(replyText);

    // Verify the reply appears in the UI (optimistic update)
    const uiItemCountAfter = await getConversationItemCount();
    expect(uiItemCountAfter).toBe(uiItemCountBefore + 1);

    // Verify a pending event was created
    const pendingEvents = await getReplyPendingEvents();
    expect(pendingEvents).toHaveLength(1);
    expect(pendingEvents[0].type).toBe(PendingEventType.ReplySent);
    expect(pendingEvents[0].data.plaintext).toBe(replyText);

    // Verify the item was added to the database
    const itemCount = await getItemCount();
    expect(itemCount).toBe(initialItemCount + 1);
  });

  it("syncs the reply event with the server", async () => {
    // Run sync to push the reply to the server
    await context.runSync();

    // Verify the pending event was cleared
    const pendingEvents = await getReplyPendingEvents();
    expect(pendingEvents).toHaveLength(0);

    // Verify the item count is still correct (reply persisted)
    const itemCount = await getItemCount();
    expect(itemCount).toBe(initialItemCount + 1);
  });

  it("handles multiple replies before sync", async () => {
    // Ensure we're on the source conversation
    await navigateToSource();

    const uiItemCountBefore = await getConversationItemCount();

    // Send multiple replies without syncing
    const replies = [
      "First batch reply",
      "Second batch reply",
      "Third batch reply",
    ];
    for (const replyText of replies) {
      await sendReply(replyText);
    }

    // Verify all replies appear in the UI
    const uiItemCountAfter = await getConversationItemCount();
    expect(uiItemCountAfter).toBe(uiItemCountBefore + replies.length);

    // Verify all pending events were created
    let pendingEvents = await getReplyPendingEvents();
    expect(pendingEvents).toHaveLength(replies.length);

    // Verify each reply has the correct plaintext
    const plaintexts = pendingEvents.map((e) => e.data.plaintext);
    for (const replyText of replies) {
      expect(plaintexts).toContain(replyText);
    }

    // Sync and verify all events are processed
    await context.runSync();

    pendingEvents = await getReplyPendingEvents();
    expect(pendingEvents).toHaveLength(0);

    // Verify all items persisted
    const itemCount = await getItemCount();
    expect(itemCount).toBe(initialItemCount + 1 + replies.length);
  });
});
