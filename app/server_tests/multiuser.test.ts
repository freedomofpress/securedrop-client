import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";
import { TestContext, TestHelpers, createDbHelper } from "./helper";
import { Crypto } from "../src/main/crypto";

const JOURNALIST_1 = "journalist";
const JOURNALIST_2 = "dellsberg";

// Source that user 1 will send a reply to and write a draft in
const REPLY_SOURCE = {
  uuid: "60a49b24-1a75-4daf-b0fa-125c1ce0d723",
  designation: "Incapable Elimination",
};

describe.sequential("multi-user session handling", () => {
  let context: TestContext;
  let helpers: TestHelpers;
  let user1InitialItemCount: number;

  beforeAll(async () => {
    context = await TestContext.setup();
    const crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
    const dbHelper = createDbHelper(crypto, context.dbPath);
    helpers = new TestHelpers(context, dbHelper);
    await context.login(JOURNALIST_1);
    await context.runSync();
    user1InitialItemCount = await helpers.getSourceItemCount(REPLY_SOURCE.uuid);
    console.log(
      `User 1 initial item count for reply source: ${user1InitialItemCount}`,
    );
  }, 180000); // 3 minutes for server startup + login

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  // User 1 actions

  it("user 1: sends a reply and syncs it to the server", async () => {
    await context.page.getByTestId(`source-${REPLY_SOURCE.uuid}`).click();
    await expect(
      context.page.getByTestId("conversation-items-container"),
    ).toBeVisible({ timeout: 5000 });

    const replyText = "Multi-user test reply from journalist";
    await context.page.getByTestId("reply-textarea").fill(replyText);
    await context.page.getByTestId("send-button").click();
    await context.page.waitForTimeout(500);

    // Verify reply was added locally
    const itemCountAfter = await helpers.getSourceItemCount(REPLY_SOURCE.uuid);
    expect(itemCountAfter).toBe(user1InitialItemCount + 1);

    // Sync to push the reply to the server
    await context.runSync();

    // All pending events should be cleared after a successful sync
    const pendingCount = await helpers.getPendingEventsCount();
    expect(pendingCount).toBe(0);
  });

  it("user 1: writes an unsent draft reply in the reply textarea", async () => {
    // Navigate to the reply source
    await context.page.getByTestId(`source-${REPLY_SOURCE.uuid}`).click();
    await expect(
      context.page.getByTestId("conversation-items-container"),
    ).toBeVisible({ timeout: 5000 });

    const draftText =
      "This draft was never sent and should be cleared on user switch";
    await context.page.getByTestId("reply-textarea").fill(draftText);
    await context.page.waitForTimeout(300);

    // Draft is visible in the textarea
    await expect(context.page.getByTestId("reply-textarea")).toHaveValue(
      draftText,
    );

    // No pending event is created for an unsent draft
    const pendingCount = await helpers.getPendingEventsCount();
    expect(pendingCount).toBe(0);
  });

  // Logout user 1

  it("logs out user 1 and returns to the sign-in screen", async () => {
    await context.logout();
  });

  // Login user 2

  it("logs in as user 2 (dellsberg)", async () => {
    await context.login(JOURNALIST_2);
  });

  it("draft state is cleared: reply textarea is empty after user switch", async () => {
    // Navigate to the same source user 1 had a draft in
    await context.page.getByTestId(`source-${REPLY_SOURCE.uuid}`).click();
    await expect(
      context.page.getByTestId("conversation-items-container"),
    ).toBeVisible({ timeout: 5000 });

    // Textarea must be empty – user 1's draft must not carry over
    await expect(context.page.getByTestId("reply-textarea")).toHaveValue("");
  });

  it("reply sent by user 1 is still present in the database for user 2", async () => {
    const itemCount = await helpers.getSourceItemCount(REPLY_SOURCE.uuid);
    expect(itemCount).toBe(user1InitialItemCount + 1);
  });

  it("pending events are cleared after successful sync", async () => {
    await context.runSync();

    const pendingCount = await helpers.getPendingEventsCount();
    expect(pendingCount).toBe(0);
  });
});
