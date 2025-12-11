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
    await page.waitForLoadState("networkidle", { timeout: 5000 });

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
    let lastOTP;
    try {
      lastOTP = fs
        .readFileSync("/tmp/app-server_tests-totp", "utf-8")
        .toString();
    } catch (_error) {
      lastOTP = "";
    }
    while (code === lastOTP) {
      // wait 1 second and try again
      await new Promise((resolve) => setTimeout(resolve, 1000));
      code = totp.generate();
    }

    // Store the code for future comparison across all instances
    fs.writeFileSync("/tmp/app-server_tests-totp", code);
    return code;
  }

  async login(): Promise<void> {
    // Wait for the sign-in page to load
    await expect(this.page.getByTestId("username-input")).toBeVisible({
      timeout: 5000,
    });

    // Fill in credentials
    await this.page.getByTestId("username-input").fill("journalist");
    await this.page
      .getByTestId("passphrase-input")
      .fill("correct horse battery staple profanity oil chewy");

    const otpCode = await this.generateTOTP();
    await this.page.getByTestId("one-time-code-input").fill(otpCode);

    // Submit login
    await this.page.getByTestId("sign-in-button").click();
    await this.page.waitForLoadState("networkidle", { timeout: 5000 });

    // Verify we're logged in by checking for sync button
    await expect(this.page.getByTestId("sync-button")).toBeVisible();
  }

  /**
   * Clicks the sync button and waits for the sync to complete.
   * Uses network idle detection to know when all API calls have finished.
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

  async navigateToSource(
    sourceUuid: string,
    expectVisible = false,
  ): Promise<void> {
    await this.context.page.getByTestId(`source-${sourceUuid}`).click();
    await this.context.page.waitForTimeout(500);
    if (expectVisible) {
      await expect(
        this.context.page.getByTestId("conversation-items-container"),
      ).toBeVisible({ timeout: 5000 });
    } else {
      // Wait for conversation area to be active (may be empty if items deleted)
      await this.context.page.waitForTimeout(500);
    }
  }

  async selectSource(uuid: string): Promise<void> {
    await this.context.page.getByTestId(`source-checkbox-${uuid}`).click();
    await this.context.page.waitForTimeout(300);
  }

  async openDeleteModal(): Promise<void> {
    await this.context.page.getByTestId("bulk-delete-button").click();
    await this.context.page.waitForTimeout(500);
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
    await this.context.page.waitForTimeout(500);
  }

  async clickDeleteConversation(): Promise<void> {
    await this.context.page
      .getByTestId("delete-modal-delete-conversation-button")
      .click();
    await this.context.page.waitForTimeout(500);
  }

  async sendReply(message: string): Promise<void> {
    await this.context.page.getByTestId("reply-textarea").fill(message);
    await this.context.page.getByTestId("send-button").click();
    await this.context.page.waitForTimeout(500);
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
      try {
        db.getItem(itemUuid);
        return true;
      } catch {
        return false;
      }
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
}
