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

export class TestContext {
  public app: ElectronApplication;
  public page: Page;
  public tempDir: string;
  public dbPath: string;

  private static lastTOTP: string | null = null;

  private constructor(
    app: ElectronApplication,
    page: Page,
    tempDir: string,
    dbPath: string,
  ) {
    this.app = app;
    this.page = page;
    this.tempDir = tempDir;
    this.dbPath = dbPath;
  }

  static async setup(): Promise<TestContext> {
    // Create a temporary directory for the database
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "securedrop-e2e-"));
    const dbPath = path.join(tempDir, ".config", "SecureDrop");
    console.log(`Using temporary database directory: ${tempDir}`);

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

    return new TestContext(app, page, tempDir, dbPath);
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
   * Generates a fresh TOTP code since the server will reject reused codes
   */
  private async generateTOTP(): Promise<string> {
    const totp = new TOTP({
      secret: "JHCOGO7VCER3EJ4L",
    });

    let code = totp.generate();

    while (code === TestContext.lastTOTP) {
      // wait 1 second and try again
      await new Promise((resolve) => setTimeout(resolve, 1000));
      code = totp.generate();
    }

    // Store the code globally for future comparison across all instances
    TestContext.lastTOTP = code;
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
   */
  async runSync(): Promise<void> {
    await this.page.getByTestId("sync-button").click();
    // TODO: let's avoid a fixed timeout here
    await this.page.waitForTimeout(3000);
  }
}
