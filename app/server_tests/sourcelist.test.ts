import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";
import { TestContext } from "./helper";

describe.sequential("source list functionality", () => {
  let context: TestContext;

  /**
   * Helper function to set the filter dropdown to a specific value
   */
  async function setFilter(filter: string): Promise<void> {
    const filterDropdown = context.page.getByTestId("filter-dropdown");
    await filterDropdown.click();
    await context.page.waitForTimeout(300);
    await context.page.getByTestId(`filter-${filter}`).click();
    await context.page.waitForTimeout(500);
  }

  beforeAll(async () => {
    context = await TestContext.setup();
  }, 180000); // 3 minutes for server startup

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("should log in and sync sources", async () => {
    // Log in with test credentials
    await context.login();

    await context.runSync();

    // Verify sources are now visible in the UI
    expect(await context.getVisibleSourceCount()).toBe(3);

    // Verify all three expected sources are displayed
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).toBeVisible();
  });

  it("should search sources by codename", async () => {
    // Get the search input
    const searchInput = context.page.getByTestId("source-search-input");
    await expect(searchInput).toBeVisible();

    // Initially all 3 sources should be visible
    expect(await context.getVisibleSourceCount()).toBe(3);

    // Search for "gorgeous" - should match "Gorgeous Apron"
    await searchInput.fill("gorgeous");
    await context.page.waitForTimeout(500); // Wait for debounce/filtering

    // Verify only one source is visible
    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();
    await expect(
      context.page.getByText("Incapable Elimination"),
    ).not.toBeVisible();
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).not.toBeVisible();

    // Search for "elimination" - should match "Incapable Elimination"
    await searchInput.clear();
    await searchInput.fill("elimination");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).not.toBeVisible();
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).not.toBeVisible();

    // Search for "preservative" - should match "Preservative Legislator"
    await searchInput.clear();
    await searchInput.fill("preservative");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).toBeVisible();
    await expect(
      context.page.getByText("Incapable Elimination"),
    ).not.toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).not.toBeVisible();

    // Clear search - all sources should be visible again
    await searchInput.clear();
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(3);
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).toBeVisible();

    // Search with no matches
    await searchInput.fill("nonexistent");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(0);
  });

  it("should search case-insensitively", async () => {
    const searchInput = context.page.getByTestId("source-search-input");

    // Test uppercase search
    await searchInput.clear();
    await searchInput.fill("GORGEOUS");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();

    // Test mixed case search
    await searchInput.clear();
    await searchInput.fill("InCaPaBlE");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();

    // Clear search
    await searchInput.clear();
  });

  it("should search by partial codename", async () => {
    const searchInput = context.page.getByTestId("source-search-input");

    // Search for partial word "apro" should match "Gorgeous Apron"
    await searchInput.fill("apro");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();

    // Search for "leg" should match "Preservative Legislator"
    await searchInput.clear();
    await searchInput.fill("leg");
    await context.page.waitForTimeout(500);

    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).toBeVisible();

    // Clear search
    await searchInput.clear();
  });

  it("should show Preservative Legislator as unread", async () => {
    // Get the Preservative Legislator source by UUID
    const preservativeLegislator = context.page.getByTestId(
      "source-designation-10e66c23-c687-40e2-b71c-2ce063fd50fe",
    );

    await expect(preservativeLegislator).toBeVisible();

    // Check that the element has font-bold class (indicates unread)
    const classes = await preservativeLegislator.getAttribute("class");
    expect(classes).toContain("font-bold");
  });

  it("should filter to show only unread sources", async () => {
    await setFilter("unread");

    // Count visible sources - should only show Preservative Legislator (unread)
    expect(await context.getVisibleSourceCount()).toBe(1);

    // Verify only Preservative Legislator is visible
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).toBeVisible();
    await expect(
      context.page.getByText("Incapable Elimination"),
    ).not.toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).not.toBeVisible();

    // Reset filter to "All"
    await setFilter("all");

    // Verify all sources are visible again
    expect(await context.getVisibleSourceCount()).toBe(3);
  });

  it("should filter to show only read sources", async () => {
    await setFilter("read");

    // Count visible sources - should show 2 read sources (Incapable Elimination and Gorgeous Apron)
    expect(await context.getVisibleSourceCount()).toBe(2);

    // Verify read sources are visible
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();

    // Verify unread source is not visible
    await expect(
      context.page.getByText("Preservative Legislator"),
    ).not.toBeVisible();

    // Reset filter to "All"
    await setFilter("all");

    // Verify all sources are visible again
    expect(await context.getVisibleSourceCount()).toBe(3);
  });
});
