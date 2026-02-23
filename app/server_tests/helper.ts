import {
  _electron as electron,
  ElectronApplication,
  Page,
  expect,
} from "@playwright/test";
import { TOTP } from "otpauth";
import fs from "node:fs";
import os from "os";
import path from "path";
import { getServerInstance, stopServerInstance } from "./server";
import { DB } from "../src/main/database";
import { Crypto } from "../src/main/crypto";
import { PendingEventType } from "../src/types";

export async function pollUntil<T>(
  fn: () => Promise<T>,
  predicate: (result: T) => boolean,
  timeout = 5000,
  interval = 100,
): Promise<T> {
  const deadline = Date.now() + timeout;
  let lastResult: T | undefined;
  while (Date.now() < deadline) {
    lastResult = await fn();
    if (predicate(lastResult)) {
      return lastResult;
    }
    await new Promise((resolve) => setTimeout(resolve, interval));
  }
  throw new Error(`pollUntil timed out after ${timeout}ms`);
}

export class TestContext {
  public app: ElectronApplication;
  public page: Page;
  public tempDir: string;
  public dbPath: string;
  public serverOrigin: string;

  private constructor(
    app: ElectronApplication,
    page: Page,
    tempDir: string,
    dbPath: string,
    serverOrigin: string,
  ) {
    this.app = app;
    this.page = page;
    this.tempDir = tempDir;
    this.dbPath = dbPath;
    this.serverOrigin = serverOrigin;
  }

  static async setup(): Promise<TestContext> {
    // Start or get the isolated server instance
    const server = await getServerInstance();
    const serverOrigin = server.origin;

    // Create a temporary directory for the database
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "securedrop-e2e-"));
    const dbPath = path.join(tempDir, ".config", "SecureDrop");
    console.log(`Using temporary database directory: ${tempDir}`);
    console.log(`Using server at: ${serverOrigin}`);

    const isCI = Boolean(process.env.CI);
    const args = ["./out/main/index.js", "--no-qubes"];

    if (isCI) {
      args.push("--no-sandbox");
    }

    const app = await electron.launch({
      args: args,
      env: {
        ...process.env,
        // Override HOME so the app uses tempDir/.config/SecureDrop for the database
        HOME: tempDir,
      },
    });

    const page = await app.firstWindow();
    await page.setViewportSize({ width: 1920, height: 1080 });
    await page.getByTestId("username-input").waitFor({ timeout: 30000 });

    return new TestContext(app, page, tempDir, dbPath, serverOrigin);
  }

  async teardown(): Promise<void> {
    if (this.app) {
      await this.app.close();
    }

    // Clean up temporary directory
    if (this.tempDir && fs.existsSync(this.tempDir)) {
      fs.rmSync(this.tempDir, { recursive: true, force: true });
    }
  }

  /**
   * Stops the server instance. Should be called in afterAll() of the last test.
   */
  static async stopServer(): Promise<void> {
    await stopServerInstance();
  }

  /**
   * Generates a fresh TOTP code since the server will reject reused codes
   */
  private async generateTOTP(): Promise<string> {
    const totp = new TOTP({
      secret: "JHCOGO7VCER3EJ4L",
    });

    let code = totp.generate();
    const totpFile = `/tmp/app-server_tests-totp-${process.pid}`;
    let lastOTP;
    try {
      lastOTP = fs.readFileSync(totpFile, "utf-8").toString();
    } catch (_error) {
      lastOTP = "";
    }
    while (code === lastOTP) {
      // wait 1 second and try again
      await new Promise((resolve) => setTimeout(resolve, 1000));
      code = totp.generate();
    }

    // Store the code for future comparison
    fs.writeFileSync(totpFile, code);
    return code;
  }

  async login(username: string = "journalist"): Promise<void> {
    await expect(this.page.getByTestId("username-input")).toBeVisible({
      timeout: 30000,
    });

    for (let attempt = 0; attempt < 3; attempt++) {
      await this.page.getByTestId("username-input").fill(username);
      await this.page
        .getByTestId("passphrase-input")
        .fill("correct horse battery staple profanity oil chewy");

      const otpCode = await this.generateTOTP();
      await this.page.getByTestId("one-time-code-input").fill(otpCode);

      // Submit login
      await this.page.getByTestId("sign-in-button").click();

      try {
        // Wait for successful login (sync button appears)
        await expect(this.page.getByTestId("sync-button")).toBeVisible({
          timeout: 15000,
        });
        return;
      } catch {
        // If we're still on the login page the credentials were rejected —
        // most likely the TOTP code expired at the window boundary.
        const onLoginPage = await this.page
          .getByTestId("username-input")
          .isVisible();
        if (onLoginPage) {
          console.warn(
            `Login attempt ${attempt + 1} failed (TOTP may have expired), retrying...`,
          );
          continue;
        }
        throw new Error(
          "Login failed: not on login page but sync button not visible",
        );
      }
    }

    throw new Error("Login failed after 3 attempts");
  }

  async logout(): Promise<void> {
    await this.page.getByTestId("sign-out-button").click();
    await expect(this.page.getByTestId("username-input")).toBeVisible({
      timeout: 15000,
    });
  }

  /**
   * Clicks the sync button and waits for the sync to complete.
   * Uses network idle detection to know when all API calls have finished.
   * DB writes in the main process happen synchronously via IPC, so they are
   * complete by the time networkidle fires.
   */
  async runSync(): Promise<void> {
    await this.page.getByTestId("sync-button").click();
    // Wait for network to become idle, indicating sync API calls have completed
    await this.page.waitForLoadState("networkidle", { timeout: 30000 });
    // Small delay to ensure database writes are flushed
    await this.page.waitForTimeout(500);
  }

  /**
   * Returns the number of sources currently rendered in the sidebar list.
   */
  async getVisibleSourceCount(): Promise<number> {
    const sourceCheckboxes = this.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    return await sourceCheckboxes.count();
  }
}

/**
 * Creates a scoped database helper that automatically closes connections.
 * This should be created once per test file with the test's crypto instance.
 */
export function createDbHelper(crypto: Crypto, dbPath: string) {
  return {
    withDb<T>(callback: (db: DB) => Promise<T> | T): Promise<T> {
      const db = new DB(crypto, dbPath);
      return Promise.resolve(callback(db)).finally(() => db.close());
    },
  };
}

/**
 * Common navigation and UI interaction helpers
 */
export class TestHelpers {
  constructor(
    private context: TestContext,
    private dbHelper: ReturnType<typeof createDbHelper>,
  ) {}

  async navigateToSource(sourceUuid: string): Promise<void> {
    // Check if the conversation is already visible (source might already be selected)
    const conversationContainer = this.context.page.getByTestId(
      "conversation-items-container",
    );
    const isAlreadyVisible = await conversationContainer
      .isVisible()
      .catch(() => false);

    if (!isAlreadyVisible) {
      // Click to select the source
      await this.context.page.getByTestId(`source-${sourceUuid}`).click();
      // Wait for conversation to load
      await expect(conversationContainer).toBeVisible({ timeout: 5000 });
    }
  }

  async selectSource(uuid: string): Promise<void> {
    const checkbox = this.context.page.getByTestId(`source-checkbox-${uuid}`);
    await checkbox.click();
    await expect(checkbox).toBeChecked({ timeout: 3000 });
  }

  async openDeleteModal(): Promise<void> {
    await this.context.page.getByTestId("bulk-delete-button").click();
    // Wait for modal content to be visible (the wrapper element may be hidden)
    await expect(
      this.context.page.getByTestId("delete-modal-content"),
    ).toBeVisible({
      timeout: 5000,
    });
  }

  async clickDeleteAccount(): Promise<void> {
    await this.context.page
      .getByTestId("delete-modal-delete-account-button")
      .click();
    // Wait for the modal to close before proceeding
    await expect(
      this.context.page.getByTestId("delete-modal-content"),
    ).not.toBeVisible({ timeout: 5000 });
  }

  async clickDeleteConversation(): Promise<void> {
    await this.context.page
      .getByTestId("delete-modal-delete-conversation-button")
      .click();
    // Wait for the modal to close before proceeding
    await expect(
      this.context.page.getByTestId("delete-modal-content"),
    ).not.toBeVisible({ timeout: 5000 });
  }

  async sendReply(message: string): Promise<void> {
    const countBefore = await this.getConversationItemCount();
    await this.context.page.getByTestId("reply-textarea").fill(message);
    await this.context.page.getByTestId("send-button").click();
    // Wait for the optimistic update to appear in the conversation
    await expect(
      this.context.page.locator('[data-testid^="item-"]'),
    ).toHaveCount(countBefore + 1, { timeout: 5000 });
  }

  async getConversationItemCount(): Promise<number> {
    const items = this.context.page.locator('[data-testid^="item-"]');
    return await items.count();
  }

  // Database query helpers
  async sourceExistsInDb(uuid: string): Promise<boolean> {
    return this.dbHelper.withDb(async (db) => {
      const source = db.getSource(uuid);
      return source !== null;
    });
  }

  async getSourceItemCount(sourceUuid: string): Promise<number> {
    return this.dbHelper.withDb(async (db) => {
      try {
        const sourceWithItems = db.getSourceWithItems(sourceUuid);
        return sourceWithItems.items.length;
      } catch {
        return 0;
      }
    });
  }

  async itemExistsInDb(itemUuid: string): Promise<boolean> {
    return this.dbHelper.withDb(async (db) => {
      const item = db.getItem(itemUuid);
      if (item) {
        return true;
      }
      return false;
    });
  }

  async getPendingEventsByType(
    type: PendingEventType,
  ): Promise<Array<{ id: string; sourceUuid?: string; itemUuid?: string }>> {
    return this.dbHelper.withDb(async (db) => {
      return db
        .getPendingEvents()
        .filter((event) => event.type === type)
        .map((event) => ({
          id: event.id,
          sourceUuid:
            "source_uuid" in event.target
              ? event.target.source_uuid
              : undefined,
          itemUuid:
            "item_uuid" in event.target ? event.target.item_uuid : undefined,
        }));
    });
  }

  async getPendingEventsCount(): Promise<number> {
    return this.dbHelper.withDb(async (db) => {
      return db.getPendingEvents().length;
    });
  }

  async waitForPendingEvents(
    type: PendingEventType,
    expectedCount: number,
    timeout = 5000,
  ): Promise<void> {
    await pollUntil(
      () => this.getPendingEventsByType(type),
      (events) => events.length === expectedCount,
      timeout,
    );
  }
}
