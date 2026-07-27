import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext } from "./helper";

describe.sequential("custom protocol", () => {
  let context: TestContext;

  beforeAll(async () => {
    context = await TestContext.setup();
  }, 120000);

  afterAll(async () => {
    await context?.teardown();
  });

  it("serves the renderer from the securedrop:// origin", async () => {
    expect(context.page.url()).toBe("securedrop://app/");
    expect(await context.page.evaluate(() => document.location.origin)).toBe(
      "securedrop://app",
    );
  });

  it("only serves allowlisted files", async () => {
    // Fetch from the main process, since the renderer's CSP forbids connecting
    // anywhere. `..` is normalized away by the URL parser, so these all end up
    // asking for paths outside of what the bundle is allowed to load.
    const statuses = await context.app.evaluate(async ({ net }) => {
      const urls = [
        "securedrop://app/",
        "securedrop://app/index.html",
        "securedrop://app/package.json",
        "securedrop://app/assets/",
        "securedrop://app/assets/nonexistent.js",
        "securedrop://app/../../package.json",
        "securedrop://app/assets/../index.html",
        "securedrop://elsewhere/index.html",
      ];
      const statuses: Record<string, number> = {};
      for (const url of urls) {
        statuses[url] = (await net.fetch(url)).status;
      }
      return statuses;
    });

    expect(statuses).toStrictEqual({
      "securedrop://app/": 200,
      "securedrop://app/index.html": 200,
      "securedrop://app/package.json": 404,
      "securedrop://app/assets/": 404,
      "securedrop://app/assets/nonexistent.js": 404,
      // Normalizes to /package.json
      "securedrop://app/../../package.json": 404,
      // Normalizes to /index.html
      "securedrop://app/assets/../index.html": 200,
      "securedrop://elsewhere/index.html": 404,
    });
  });

  it("applies the CSP to the document", async () => {
    const csp = await context.app.evaluate(async ({ net }) => {
      const response = await net.fetch("securedrop://app/");
      return response.headers.get("content-security-policy");
    });
    expect(csp).toContain("default-src 'none'");
    expect(csp).toContain("script-src 'self'");

    // And it's enforced: an inline script with no nonce must not execute
    const ran = await context.page.evaluate(() => {
      const script = document.createElement("script");
      script.textContent = "window.__cspBypassed = true;";
      document.body.appendChild(script);
      script.remove();
      return "__cspBypassed" in window;
    });
    expect(ran).toBe(false);
  });

  it("blocks all navigation", async () => {
    // The renderer is a single document; it has no reason to navigate at all,
    // to its own origin or anywhere else.
    for (const url of ["https://example.com/", "securedrop://app/index.html"]) {
      await context.page.evaluate((target) => {
        window.location.href = target;
      }, url);
      // Give the (blocked) navigation a chance to happen
      await context.page.waitForTimeout(1000);
      expect(context.page.url()).toBe("securedrop://app/");
    }
  });

  it("blocks redirects", async () => {
    // `loadURL` doesn't emit `will-navigate`, so a redirect it receives is only
    // catchable via `will-redirect`. Intercept http rather than the app's own
    // scheme, so the real protocol handler is left intact for other tests.
    const before = context.page.url();
    await context.app.evaluate(async ({ protocol, BrowserWindow }) => {
      protocol.handle("http", async () =>
        Response.redirect("https://example.com/", 302),
      );
      try {
        await BrowserWindow.getAllWindows()[0]
          .loadURL("http://redirector.test/")
          .catch(() => {});
      } finally {
        protocol.unhandle("http");
      }
    });
    await context.page.waitForTimeout(2000);
    expect(context.page.url()).toBe(before);
  });
});
