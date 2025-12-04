import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";

import { TestContext } from "./helper";
import { DB } from "../src/main/database";
import { Crypto } from "../src/main/crypto";
import { PendingEventType } from "../src/types";

const TARGET_SOURCE = {
  uuid: "60a49b24-1a75-4daf-b0fa-125c1ce0d723",
  designation: "Incapable Elimination",
};

async function setFilter(context: TestContext, filter: string): Promise<void> {
  const filterDropdown = context.page.getByTestId("filter-dropdown");
  await filterDropdown.click();
  await context.page.waitForTimeout(300);
  await context.page.getByTestId(`filter-${filter}`).click();
  await context.page.waitForTimeout(500);
}

describe.sequential("starring sources", () => {
  let context: TestContext;
  let crypto: Crypto;

  function withDb<T>(callback: (db: DB) => Promise<T> | T): Promise<T> {
    const db = new DB(crypto, context.dbPath);
    return Promise.resolve(callback(db)).finally(() => db.close());
  }

  async function getStarPendingEvents(): Promise<PendingEventType[]> {
    return withDb(async (db) => {
      return db
        .getPendingEvents()
        .filter(
          (event) =>
            event.type === PendingEventType.Starred ||
            event.type === PendingEventType.Unstarred,
        )
        .filter((event) => {
          if ("source_uuid" in event.target) {
            return event.target.source_uuid === TARGET_SOURCE.uuid;
          }
          return false;
        })
        .map((event) => event.type);
    });
  }

  async function isSourceStarred(): Promise<boolean> {
    return withDb(async (db) => {
      const source = db.getSource(TARGET_SOURCE.uuid);
      // SQLite stores booleans as integers; coerce to actual boolean
      return Boolean(source?.data.is_starred);
    });
  }

  async function toggleStar(): Promise<void> {
    await context.page.getByTestId(`star-button-${TARGET_SOURCE.uuid}`).click();
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
  }, 90000); // 90 seconds for server startup + login

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("stars a source locally and queues an event", async () => {
    await setFilter(context, "starred");
    expect(await context.getVisibleSourceCount()).toBe(0);

    await setFilter(context, "all");
    await toggleStar();

    await setFilter(context, "starred");
    expect(await context.getVisibleSourceCount()).toBe(1);
    await expect(
      context.page.getByText(TARGET_SOURCE.designation),
    ).toBeVisible();

    const pendingTypes = await getStarPendingEvents();
    expect(pendingTypes).toEqual([PendingEventType.Starred]);
    expect(await isSourceStarred()).toBe(true);
  });

  it("syncs the star event with the server", async () => {
    await context.runSync();

    const pendingTypes = await getStarPendingEvents();
    expect(pendingTypes).toHaveLength(0);

    expect(await isSourceStarred()).toBe(true);
  });

  it("unstars the source and restores initial state", async () => {
    await setFilter(context, "all");
    await toggleStar();

    await setFilter(context, "starred");
    expect(await context.getVisibleSourceCount()).toBe(0);

    let pendingTypes = await getStarPendingEvents();
    expect(pendingTypes).toEqual([PendingEventType.Unstarred]);

    await context.runSync();

    pendingTypes = await getStarPendingEvents();
    expect(pendingTypes).toHaveLength(0);
    expect(await isSourceStarred()).toBe(false);
  });
});
