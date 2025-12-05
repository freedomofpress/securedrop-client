import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";
import { TestContext } from "./helper";
import { DB } from "../src/main/database";
import { Crypto } from "../src/main/crypto";

// Expected database index after sync (from data.yaml)
const EXPECTED_INDEX = {
  items: {
    "127b98a7-2976-45a9-8dde-dd50602bffbb":
      "d85a7f7f4f2d6ce1ef509ef35914000b50e37b6137f4ab0f1b54d4094610d446",
    "2c287eff-a397-46d0-905f-8842147d183d":
      "d0112b7e54e17a5a4ff961a881022cb59266c6ca96dffda3a7fbdc9b91d40ab5",
    "31eeac69-e02f-46f1-a5da-b8f912eb773d":
      "e1283a70068e11bbbd0118de60b4a6cea1ae5afea54a46f2e2d4d9d33e4d7faa",
    "3f3d5d05-e758-4cbb-9ea0-876d7152fd7f":
      "9b87cdb1972aaa5bffdd4f4b25179a56f8ff20ff2a0080e347deb7b3490c8230",
    "40e13a88-5409-4201-9495-d06c335e203f":
      "0161ca6ed0a8b1358318c4e1b06683026c3071977e9a25ea166bc672751a93fa",
    "48256b37-2761-4695-8a1a-282601dc3c87":
      "ccd8c21a34242ce4c1a80c544e14185d95f2bf13f64ab3c912b327cbb7786e15",
    "485396d7-114b-49d5-a910-43337f72b471":
      "082b57f9d5d68f26831ebf45b80613ef9ed71b61d58dc235f6454c3fe1fa73df",
    "6428c271-3108-4c73-9a44-9acfb7e2b388":
      "cb48aa754a95005a9aac025da999921fc827809bd1d8ce5a37addaee4b63651b",
    "6ba8a2c8-aa3a-4b0e-95f9-34d3001a5043":
      "3b0c1ed872a48af2c52731e14b7acfe41f484e7fc2209cbece5c0cdb1428389b",
    "85f0d337-b077-41b6-a914-33fee7bfcaa1":
      "4afcdbafe6137a9713e600d081b31bf1340c5479c2074b474e857236b66dedbd",
    "96325861-741a-41eb-91b5-bb1ff34f3e70":
      "eb855e9bb8e229e8fc2059ed8dbcbf56c4c8b51fcaa91648c7124689c2b23a00",
    "a500332a-52dd-4296-a8e7-213cb575d9ff":
      "a3fed81fa4c919b5a1cc8aeea3baa25d81892b9ae17015e77b9b6bdd374cbec9",
    "adca50a5-9f70-49db-a5ae-0c184b54c6ed":
      "a4b28cfc1e0b5618f861b876a17b86e1db3e820926a5464173a43c7993ade150",
    "b8260d37-87b2-49b3-a235-bac31c11021d":
      "32a25d050a42f5c516471d053298a0f983a734da71a43e6a9ff74e6a37b1306b",
    "cc1be744-8a71-4e52-92e7-51315b6cb643":
      "b000f98dce565a34f396e770585dde3b1aeded1f01d1ab7299e5928892fb6c5a",
    "d6dc8fb4-582f-4cfc-b466-19e4b402b3ae":
      "0334c660614d27baea4b821586986c006596dfc3cd8a6affa687a937f39aa05a",
    "d8782e98-0cbd-4142-850d-6bcefabb8237":
      "31d1e43cfd3e0dc833bc83808ac5e98277eacfa005215443b7b304e4ee9ecb5e",
    "f53f43d9-41fa-42a6-88b0-6529aaacc599":
      "53cfb9f81e976d81a40d712cb2246ca08b890e743797a1e3b4c554410a2a28e3",
  },
  journalists: {
    "72eb04dc-7596-4bc0-a9b1-a0f5648f04f0":
      "3a92ab74ac77712f7ca3a17678bb46396c5de4b63c19cd4333edd3325864197b",
    "be726875-1290-49d4-922d-2fc0901c9266":
      "8877384bc11f5996adaec4aef2741db136a85661853ad2e0c01a4843af7f3f26",
    "e32be48a-67b9-4516-834a-69fbe0f14d10":
      "9a0195b7838daef20d71a13633fb98d7800677a089f06c63fd63985e03916a2c",
  },
  sources: {
    "10e66c23-c687-40e2-b71c-2ce063fd50fe":
      "6a03444cc38bfe29cbf110199ab50132d498e1db08146257fcc4a48b7741140d",
    "60a49b24-1a75-4daf-b0fa-125c1ce0d723":
      "0931a1421b00279e4c473770d43d05cef33b266f630fc28c2d75f819d934f680",
    "6d3a8b24-a7ec-4c8e-b646-36782b52d77e":
      "f3778ac54865db25b71320fe419402e484f67e98f0eefb0ee45cf77b93235e90",
  },
};

const EXPECTED_VERSION =
  "5b4388514c7e5c4dcb57aacb8efad7596e83c6b0b5eab4dfea631056b0177a5a";

describe.sequential("sync against a real server", () => {
  let context: TestContext;
  let firstSyncVersion: string;
  let crypto: Crypto;

  beforeAll(async () => {
    context = await TestContext.setup();
    crypto = Crypto.initialize({
      isQubes: false,
      submissionKeyFingerprint: "",
    });
  }, 180000); // 3 minutes for server startup

  afterAll(async () => {
    await context.teardown();
    await TestContext.stopServer();
  }, 60000);

  it("should start with a fresh empty database", async () => {
    // Wait for the sign-in page to load
    await expect(context.page.getByTestId("username-input")).toBeVisible({
      timeout: 5000,
    });

    await context.page.getByTestId("use-offline-button").click();

    await context.page.waitForLoadState("networkidle", { timeout: 5000 });

    // Verify no sources in UI by looking at the source checkboxes
    const sourceCheckboxes = context.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    const count = await sourceCheckboxes.count();
    expect(count).toBe(0);

    // Verify empty state message
    await expect(
      context.page.getByText("Select a source from the list"),
    ).toBeVisible();

    // Verify database is empty
    const db = new DB(crypto, context.dbPath);
    const index = db.getIndex();

    expect(Object.keys(index.sources).length).toBe(0);
    expect(Object.keys(index.items).length).toBe(0);
    expect(Object.keys(index.journalists).length).toBe(0);

    db.close();
  });

  it("should successfully log in with valid credentials", async () => {
    // Navigate back to sign-in page
    await context.page.getByTestId("signin-form-button").click();
    await context.page.waitForLoadState("networkidle", { timeout: 5000 });

    // Log in with test credentials
    await context.login();
  });

  it("should verify logged-in journalist from Redux state", async () => {
    // Verify journalist info from Redux state
    const reduxState = await context.page.evaluate(() => {
      const store = (window as any).__REDUX_STORE__;
      if (!store) {
        throw new Error("Redux store not found on window object");
      }
      return store.getState();
    });
    // SessionStatus.Auth == 2, TODO import that type
    expect(reduxState.session.status).toBe(2);
    expect(reduxState.session.authData.journalistUUID).toBe(
      "be726875-1290-49d4-922d-2fc0901c9266",
    );
  });

  it("should sync and populate database with sources", async () => {
    await context.runSync();

    // Verify sources are now visible in the UI
    const sourceCheckboxes = context.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    const sourceCount = await sourceCheckboxes.count();
    expect(sourceCount).toBe(3);

    // Verify expected sources are displayed
    await expect(context.page.getByText("Incapable Elimination")).toBeVisible();
    await expect(context.page.getByText("Gorgeous Apron")).toBeVisible();

    // Query the database to verify it matches expected index
    const db = new DB(crypto, context.dbPath);
    const index = db.getIndex();
    firstSyncVersion = db.getVersion();

    expect(index).toEqual(EXPECTED_INDEX);
    expect(firstSyncVersion).toBe(EXPECTED_VERSION);

    db.close();
  });

  it("should be idempotent when syncing again", async () => {
    await context.runSync();

    // Verify sources count is still the same
    const sourceCheckboxes = context.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    const sourceCount = await sourceCheckboxes.count();
    expect(sourceCount).toBe(3);

    // Verify database version stayed the same (idempotent)
    const db = new DB(crypto, context.dbPath);
    const secondVersion = db.getVersion();
    expect(secondVersion).toBe(firstSyncVersion);
    expect(secondVersion).toBe(EXPECTED_VERSION);
    db.close();
  });
});
