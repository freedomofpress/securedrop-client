#!/usr/bin/env node

import { _electron as electron } from "playwright";
import { existsSync, mkdirSync } from "fs";
import { join } from "path";
import TranslationExtractor from "./extractor.js";

/**
 * Clean API for automated translation screenshots
 */
class TranslationScreenshotAPI {
  constructor(options = {}) {
    this.app = null;
    this.page = null;
    this.outputDir = options.outputDir || "./screenshots";
    this.currentContext = null;
    this.extractor = new TranslationExtractor();
    this.screenshotState = new Set(); // Track taken screenshots
    this.allAttemptedKeys = new Set(); // Track all keys we've tried

    // Ensure output directory exists
    if (!existsSync(this.outputDir)) {
      mkdirSync(this.outputDir, { recursive: true });
    }
  }

  /**
   * Initialize and launch the Electron app
   */
  async launch() {
    console.log("Launching Electron app...");

    const args = ["./out/main/index.js", "--no-qubes"];
    const isCI = Boolean(process.env.CI);

    if (isCI) {
      args.push("--no-sandbox");
      console.log("Running in CI mode, disabling sandbox");
    }

    this.app = await electron.launch({
      args: args,
      headless: isCI,
    });

    this.page = await this.app.firstWindow();
    await this.page.setViewportSize({ width: 1920, height: 1080 });
    await this.page.waitForLoadState("networkidle");

    console.log("App launched at 1920x1080");
  }

  /**
   * Set the current translation context/namespace
   * @param {string} namespace - Translation namespace (e.g., "SignIn", "MainContent")
   */
  context(namespace) {
    this.currentContext = namespace;
    console.log(`Set context to: ${namespace}`);
  }

  /**
   * Navigate to a specific route
   * @param {string} route - Route to navigate to (e.g., "#/signin")
   */
  async navigate(route) {
    console.log(`Navigating to: ${route}`);

    if (route.startsWith("#")) {
      // Client-side routing
      const currentUrl = this.page.url();
      const baseUrl = currentUrl.split("#")[0];
      await this.page.goto(`${baseUrl}${route}`);
    } else {
      await this.page.goto(route);
    }

    await this.page.waitForLoadState("networkidle");
  }

  /**
   * Get element by test ID
   * @param {string} testId - data-testid attribute value, use * for wildcard suffix
   * @returns {Object} Element wrapper with helper methods
   */
  getByTestId(testId) {
    let element;
    if (testId.endsWith("*")) {
      // Handle wildcard matches like "star-button-*"
      const prefix = testId.replace("*", "");
      element = this.page.locator(`[data-testid^="${prefix}"]`).first();
    } else {
      // Exact match
      element = this.page.getByTestId(testId);
    }

    const page = this.page;

    return {
      async setValue(value) {
        console.log(`Setting value "${value}" on element: ${testId}`);
        await element.fill(value);
      },

      async click() {
        console.log(`Clicking element: ${testId}`);
        await element.click();
        await page.waitForLoadState("networkidle");
      },

      async hover() {
        console.log(`Hovering over element: ${testId}`);
        await element.hover();
        // Wait a moment for tooltip to appear
        await page.waitForTimeout(500);
      },
    };
  }

  /**
   * Reload the current page
   */
  async reload() {
    console.log("Reloading page...");
    await this.page.reload();
    await this.page.waitForLoadState("networkidle");
  }

  /**
   * Take screenshots for all available translation keys in current context
   * Only takes screenshots that haven't been taken yet
   */
  async takeScreenshots() {
    if (!this.currentContext) {
      throw new Error("No context set. Call context(namespace) first.");
    }

    console.log(`Taking screenshots for context: ${this.currentContext}`);

    // Dynamically generate translation keys (no disk file needed)
    const translationKeys = this.extractor.extractNamespaceKeys(
      this.currentContext,
    );
    const availableKeys = Object.keys(translationKeys);

    console.log(`Found ${availableKeys.length} keys in context`);

    let attempted = 0;
    let successful = 0;
    let skipped = 0;

    for (const [shortKey, data] of Object.entries(translationKeys)) {
      const screenshotId = `${this.currentContext}.${shortKey}`;

      // Track that we've attempted this key
      this.allAttemptedKeys.add(screenshotId);

      // Skip if already taken
      if (this.screenshotState.has(screenshotId)) {
        skipped++;
        continue;
      }

      attempted++;
      const success = await this._takeScreenshot(
        shortKey,
        data,
        this.currentContext,
      );

      if (success) {
        successful++;
        this.screenshotState.add(screenshotId);
      }
    }

    // Simple progress output (no detailed results)
    if (attempted > 0) {
      console.log(
        `Context ${this.currentContext}: ${successful}/${attempted} new screenshots (${skipped} already taken)\n`,
      );
    }
  }

  /**
   * Internal method to take a single screenshot
   */
  async _takeScreenshot(shortKey, data, context) {
    const name = `${shortKey} ("${data.processedText}")`;

    // Clear any existing highlights
    await this._clearAllHighlights();

    // Find the element
    const element = await this._findElementByText(data.processedText);
    if (!element) {
      console.log(`Not found: ${name}`);
      return false;
    }

    try {
      // Highlight and screenshot
      await element.scrollIntoViewIfNeeded();
      await this._highlightElement(element);
      await this.page.waitForTimeout(200);

      const filename = `${context}.${shortKey}.png`;
      const filepath = join(this.outputDir, filename);

      await this.page.screenshot({
        path: filepath,
        fullPage: true,
      });

      await this._clearAllHighlights();

      console.log(`Saved: ${name} - ${filepath}`);
      return true;
    } catch (error) {
      console.log(`Error (${name}): ${error.message}`);
      await this._clearAllHighlights();
      return false;
    }
  }

  /**
   * Find element by text
   */
  async _findElementByText(text) {
    // Try exact match first
    let element = await this._findElementByTextExact(text);
    if (element) return element;

    // If text contains HTML tags, try with tags stripped
    if (text.includes("<") && text.includes(">")) {
      const strippedText = text.replace(/<[^>]*>/g, "");
      element = await this._findElementByTextExact(strippedText);
      if (element) return element;
    }

    return null;
  }

  /**
   * Find element by exact text match
   */
  async _findElementByTextExact(text) {
    const candidates = await this.page.evaluate(
      ([searchText]) => {
        const allElements = document.querySelectorAll("*");
        const matches = [];

        function getXPath(element) {
          if (element.id !== "") {
            return `//*[@id="${element.id}"]`;
          }
          if (element === document.body) {
            return "/html/body";
          }

          let ix = 0;
          const siblings = element.parentNode?.childNodes || [];
          for (let i = 0; i < siblings.length; i++) {
            const sibling = siblings[i];
            if (sibling === element) {
              const tagName = element.tagName.toLowerCase();
              const index = ix > 0 ? `[${ix + 1}]` : "";
              return getXPath(element.parentNode) + "/" + tagName + index;
            }
            if (sibling.nodeType === 1 && sibling.tagName === element.tagName) {
              ix++;
            }
          }
        }

        for (const el of allElements) {
          const directText = el.childNodes
            ? Array.from(el.childNodes)
                .filter((node) => node.nodeType === Node.TEXT_NODE)
                .map((node) => node.textContent.trim())
                .join(" ")
                .trim()
            : "";

          const fullText = el.textContent?.trim() || "";

          // Also check placeholder attribute for input elements
          const placeholderText = el.placeholder?.trim() || "";

          if (
            directText === searchText ||
            fullText === searchText ||
            placeholderText === searchText
          ) {
            const rect = el.getBoundingClientRect();
            if (rect.width > 0 && rect.height > 0) {
              matches.push({
                tagName: el.tagName.toLowerCase(),
                directText: directText,
                placeholderText: placeholderText,
                matchType:
                  placeholderText === searchText ? "placeholder" : "text",
                area: rect.width * rect.height,
                xpath: getXPath(el),
              });
            }
          }
        }

        return matches;
      },
      [text],
    );

    if (candidates.length === 0) {
      return null;
    }

    // Pick the best candidate (prefer direct text match, then placeholder, then smallest area)
    const bestCandidate = candidates.reduce((best, current) => {
      // Priority: direct text > placeholder > full text
      const bestDirectMatch = best.directText === text;
      const currentDirectMatch = current.directText === text;
      const bestPlaceholderMatch = best.placeholderText === text;
      const currentPlaceholderMatch = current.placeholderText === text;

      // Direct text matches are highest priority
      if (currentDirectMatch && !bestDirectMatch) {
        return current;
      }
      if (bestDirectMatch && !currentDirectMatch) {
        return best;
      }

      // If both/neither are direct matches, prefer placeholder matches
      if (currentPlaceholderMatch && !bestPlaceholderMatch) {
        return current;
      }
      if (bestPlaceholderMatch && !currentPlaceholderMatch) {
        return best;
      }

      // If same match type, prefer smaller area
      return current.area < best.area ? current : best;
    });

    try {
      const element = this.page.locator(`xpath=${bestCandidate.xpath}`);
      const count = await element.count();
      if (count > 0) {
        return element.first();
      }
    } catch (e) {
      console.log(`XPath lookup failed: ${e.message}`);
    }

    return null;
  }

  /**
   * Highlight an element with red border and padding
   */
  async _highlightElement(element) {
    await element.evaluate((el) => {
      el.style.border = "2px solid red";
      el.style.borderRadius = "4px";
      el.style.boxShadow = "0 0 8px rgba(255, 0, 0, 0.4)";
      el.style.padding = "4px";
      el.style.position = "relative";
      el.style.zIndex = "9999";
      el.dataset.playwrightHighlight = "true";
    });
  }

  /**
   * Clear all highlights from the page
   */
  async _clearAllHighlights() {
    await this.page.evaluate(() => {
      const highlightedElements = document.querySelectorAll(
        "[data-playwright-highlight]",
      );
      highlightedElements.forEach((el) => {
        el.style.border = "";
        el.style.borderRadius = "";
        el.style.boxShadow = "";
        el.style.padding = "";
        el.style.position = "";
        el.style.zIndex = "";
        delete el.dataset.playwrightHighlight;
      });
    });
  }

  /**
   * Print final summary report
   */
  printFinalReport() {
    console.log("\n=== Final Report ===");
    console.log(`Total screenshots taken: ${this.screenshotState.size}`);

    // Calculate unfound keys: attempted but not captured
    const unfoundKeys = [...this.allAttemptedKeys].filter(
      (key) => !this.screenshotState.has(key),
    );

    if (unfoundKeys.length > 0) {
      console.log(`\nKeys never found (${unfoundKeys.length}):`);
      unfoundKeys.sort().forEach((key) => {
        console.log(`  ❌ ${key}`);
      });
    } else {
      console.log("\n✅ All translation keys were found and captured!");
    }
  }

  /**
   * Close the app
   */
  async close() {
    if (this.app) {
      await this.app.close();
      console.log("App closed");
    }
  }
}

export default TranslationScreenshotAPI;
