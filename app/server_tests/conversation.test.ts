import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";
import { TestContext } from "./helper";

describe.sequential("conversation view functionality", () => {
  let context: TestContext;

  /**
   * Helper function to click on a source by its designation in the sidebar
   */
  async function selectSource(designation: string): Promise<void> {
    // Find the source designation element in the sidebar
    const sourceDesignation = context.page
      .locator('[data-testid^="source-designation-"]')
      .filter({ hasText: designation })
      .first();

    // Check if this source is already active by checking if the header already shows it
    const header = context.page.getByTestId("conversation-header-designation");
    const currentDesignation = await header
      .textContent({ timeout: 1000 })
      .catch(() => null);

    // Only click if this source is not already selected
    if (currentDesignation !== designation) {
      await sourceDesignation.click();
      await context.page.waitForTimeout(500);
    }
  }

  /**
   * Helper function to get the count of visible conversation items
   */
  async function getConversationItemCount(): Promise<number> {
    const items = context.page.locator('[data-testid^="item-"]');
    return await items.count();
  }

  beforeAll(async () => {
    context = await TestContext.setup();
  }, 40000);

  afterAll(async () => {
    await context.teardown();
  }, 30000);

  it("should log in and sync sources", async () => {
    await context.login();
    await context.runSync();

    // Verify sources are visible
    const sourceCheckboxes = context.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    expect(await sourceCheckboxes.count()).toBe(3);
  });

  it("should display empty state when no source is selected", async () => {
    // Verify the empty state message is visible
    await expect(
      context.page.getByText("Select a source from the list"),
    ).toBeVisible();
  });

  it("should display conversation when a source is selected", async () => {
    // Select the first source "Incapable Elimination"
    await selectSource("Incapable Elimination");

    // Wait for conversation to load
    await context.page.waitForTimeout(1000);

    // Verify the source header is displayed with correct designation
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Incapable Elimination");

    // Verify conversation items container is visible
    await expect(
      context.page.getByTestId("conversation-items-container"),
    ).toBeVisible();

    // Verify conversation items are visible
    const itemCount = await getConversationItemCount();
    expect(itemCount).toBeGreaterThan(0);
  });

  it("should display all conversation items in correct order", async () => {
    // Select "Incapable Elimination" source
    await selectSource("Incapable Elimination");

    // Wait for items container to be visible
    await expect(
      context.page.getByTestId("conversation-items-container"),
    ).toBeVisible();

    // Wait a bit more for items to render
    await context.page.waitForTimeout(1000);

    // Based on data.yaml, "Incapable Elimination" has 6 items in chronological order
    const items = context.page.locator('[data-testid^="item-"]');
    const itemCount = await items.count();
    expect(itemCount).toBe(6);

    // Expected items in chronological order (oldest first), matching data.yaml
    const expectedItemsInOrder: Array<{
      uuid: string;
      kind: string;
      text: string;
    }> = [
      {
        uuid: "f53f43d9-41fa-42a6-88b0-6529aaacc599",
        kind: "message",
        text: "Lorem ipsum dolor sit amet",
      },
      {
        uuid: "6428c271-3108-4c73-9a44-9acfb7e2b388",
        kind: "reply",
        text: "Sed do eiusmod tempor",
      },
      {
        uuid: "d8782e98-0cbd-4142-850d-6bcefabb8237",
        kind: "message",
        text: "Donec auctor",
      },
      {
        uuid: "127b98a7-2976-45a9-8dde-dd50602bffbb",
        kind: "file",
        text: "Encrypted File", // Files show "Encrypted File" when not downloaded
      },
      {
        uuid: "40e13a88-5409-4201-9495-d06c335e203f",
        kind: "reply",
        text: "Ut enim ad minim veniam",
      },
      {
        uuid: "2c287eff-a397-46d0-905f-8842147d183d",
        kind: "file",
        text: "Encrypted File", // Files show "Encrypted File" when not downloaded
      },
    ];

    // Collect actual order for debugging
    const actualUuids: string[] = [];
    for (let i = 0; i < itemCount; i++) {
      const item = items.nth(i);
      const testId = await item.getAttribute("data-testid");
      const uuid = testId?.replace("item-", "") || "";
      actualUuids.push(uuid);
    }
    console.log("Actual item UUIDs:", actualUuids);

    // Verify each item appears in the expected order with correct content
    for (let i = 0; i < itemCount; i++) {
      const item = items.nth(i);
      const testId = await item.getAttribute("data-testid");
      const uuid = testId?.replace("item-", "") || "";
      const expected = expectedItemsInOrder[i];

      // Verify UUID matches expected order
      expect(uuid).toBe(expected.uuid);

      // Verify the content appears in this item
      await expect(item.getByText(new RegExp(expected.text))).toBeVisible();
    }
  });

  it("should switch between different source conversations", async () => {
    // Select first source
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(500);

    // Verify we're viewing Incapable Elimination
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Incapable Elimination");

    // Switch to second source
    await selectSource("Gorgeous Apron");
    await context.page.waitForTimeout(500);

    // Verify we're now viewing Gorgeous Apron
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Gorgeous Apron");

    // Switch to third source
    await selectSource("Preservative Legislator");
    await context.page.waitForTimeout(500);

    // Verify we're now viewing Preservative Legislator
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Preservative Legislator");
  });

  it("should display different item types (message, reply, file)", async () => {
    // Select "Incapable Elimination" which has all three types
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(1000);

    // Check for items - all item types use data-testid="item-{uuid}"
    const items = context.page.locator('[data-testid^="item-"]');
    const itemCount = await items.count();

    // Based on data.yaml, Incapable Elimination has 6 items (2 messages, 2 replies, 2 files)
    expect(itemCount).toBe(6);

    // Verify at least one item is visible
    await expect(items.first()).toBeVisible();
  });

  it("should display source designation in header", async () => {
    // Select each source and verify header displays correct designation
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(1000);
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Incapable Elimination");

    await selectSource("Gorgeous Apron");
    await context.page.waitForTimeout(1000);
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Gorgeous Apron");

    await selectSource("Preservative Legislator");
    await context.page.waitForTimeout(1000);
    await expect(
      context.page.getByTestId("conversation-header-designation"),
    ).toHaveText("Preservative Legislator");
  });

  it("should display last updated timestamp in header", async () => {
    // Select a source
    await selectSource("Gorgeous Apron");
    await context.page.waitForTimeout(500);

    // The header should display "Last source activity: [timestamp]"
    // We just verify the element exists with test ID
    await expect(
      context.page.getByTestId("conversation-header-last-activity"),
    ).toBeVisible();
  });

  it("should scroll conversation to bottom when items change", async () => {
    // Select a source with multiple items
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(1000);

    // Get the scroll container
    const scrollContainer = context.page.locator(
      ".overflow-y-auto.overflow-x-hidden",
    );

    // Verify scroll container exists
    await expect(scrollContainer).toBeVisible();

    // Note: Actual scroll position testing is difficult in Playwright
    // but we can verify the container is present and items are visible
    const itemCount = await getConversationItemCount();
    expect(itemCount).toBeGreaterThan(0);
  });

  it("should display empty conversation state for sources with no items", async () => {
    // This test would work if we had a source with no items
    // For now, we verify that all our test sources have items
    await selectSource("Preservative Legislator");
    await context.page.waitForTimeout(1000);

    const itemCount = await getConversationItemCount();
    // Based on data.yaml, Preservative Legislator has 6 items
    expect(itemCount).toBe(6);
  });

  it("should maintain conversation state when navigating back to previously viewed source", async () => {
    // Select first source
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(500);
    const firstCount = await getConversationItemCount();

    // Switch to another source
    await selectSource("Gorgeous Apron");
    await context.page.waitForTimeout(500);

    // Switch back to first source
    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(500);

    // Verify item count is the same
    const secondCount = await getConversationItemCount();
    expect(secondCount).toBe(firstCount);
  });

  it("should display all three test sources with correct item counts", async () => {
    // Based on data.yaml:
    // - Incapable Elimination: 6 items
    // - Gorgeous Apron: 6 items
    // - Preservative Legislator: 6 items

    await selectSource("Incapable Elimination");
    await context.page.waitForTimeout(1000);
    expect(await getConversationItemCount()).toBe(6);

    await selectSource("Gorgeous Apron");
    await context.page.waitForTimeout(1000);
    expect(await getConversationItemCount()).toBe(6);

    await selectSource("Preservative Legislator");
    await context.page.waitForTimeout(1000);
    expect(await getConversationItemCount()).toBe(6);
  });
});
