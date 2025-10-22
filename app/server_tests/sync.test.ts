import { describe, it, beforeAll, afterAll } from "vitest";
import { expect } from "@playwright/test";
import { TestContext } from "./helper";
import { DB } from "../src/main/database";

// Expected database index after sync (from data.yaml)
const EXPECTED_INDEX = {
  items: {
    "127b98a7-2976-45a9-8dde-dd50602bffbb":
      "63c5577e45f2aea717faa6b0bf76b75f055e2b0b0d59d8b420e6dae86252fdff",
    "2c287eff-a397-46d0-905f-8842147d183d":
      "1ee6630c0ed2d72d47745a6efd386d8ee13435ef8f34c4f34bd6820f2802609d",
    "31eeac69-e02f-46f1-a5da-b8f912eb773d":
      "d86ba53163a22962d5ed06450bc32fb15d741321c29429df634f237679ae6a97",
    "3f3d5d05-e758-4cbb-9ea0-876d7152fd7f":
      "56e230a0092330f8fcf766b38e9db26b0c2922b95c13f5a715d56247be4fa6a9",
    "40e13a88-5409-4201-9495-d06c335e203f":
      "e3dcacad557d7ae1793310a60ea102256e7da152f679534fb97e2f10cdcf09be",
    "48256b37-2761-4695-8a1a-282601dc3c87":
      "c3e16593cbedd5c6f375fbe10589b632333a300274c1a0b0c678a85f1a83cbee",
    "485396d7-114b-49d5-a910-43337f72b471":
      "ff750d59ee19a102ba87babf44b0559472e5e8195afd08381ffe09a21efa2dad",
    "6428c271-3108-4c73-9a44-9acfb7e2b388":
      "7d5d7f2ac75064a2c53942a28327e91e726304bfd9d4df3f9de91723cabdf236",
    "6ba8a2c8-aa3a-4b0e-95f9-34d3001a5043":
      "1b9822810e599583a7408a5b177c1e131b40c8511431ed76045302211ef185aa",
    "85f0d337-b077-41b6-a914-33fee7bfcaa1":
      "cdceb7677c988d53603f488a6c8c0e085ec36bbfed8366e34612dbaa67ed5d11",
    "96325861-741a-41eb-91b5-bb1ff34f3e70":
      "75574ca96c77f3bd998fccb0e6d277b6a02fe2e111cd889479c25f2a47396b1f",
    "a500332a-52dd-4296-a8e7-213cb575d9ff":
      "f956889a56ea2deee51a2fed81500cbc16ea5e9864074d6409a2391f9fe40da7",
    "adca50a5-9f70-49db-a5ae-0c184b54c6ed":
      "9cad7eae6d5c541358a45cacc9836fa9b0d571cf5dfa120b6f6a24c12c42f410",
    "b8260d37-87b2-49b3-a235-bac31c11021d":
      "0a488644b629e928785ce7a739484959af01cf87ddf6b0490f751b20a284e831",
    "cc1be744-8a71-4e52-92e7-51315b6cb643":
      "f8daf758f68a8edb84d4ec822cee0137ea18a9339de54ab8558cbdbb13fdcc82",
    "d6dc8fb4-582f-4cfc-b466-19e4b402b3ae":
      "142638535ef1b2cd07e92daac98c07e821826b2e60d2fc78454dc0db9ca9fa8b",
    "d8782e98-0cbd-4142-850d-6bcefabb8237":
      "f290cbc0216c9dafd504f421bf617df1ef7746c44857f94ffbc3c03c0b61e649",
    "f53f43d9-41fa-42a6-88b0-6529aaacc599":
      "ce941de7427623d9ca1c2716af3a3bdc4500ff0d577ac95ffaec3320ea978e87",
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
  "29c5fd7d4fdc32c766c56cd3282bf7d66f6a0a4cc5bfae7ce1c8c3f362dbc4bf";

describe.sequential("sync against a real server", () => {
  let context: TestContext;
  let firstSyncVersion: string;

  beforeAll(async () => {
    context = await TestContext.setup();
  }, 40000);

  afterAll(async () => {
    await context.teardown();
  }, 20000);

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
    const db = new DB(context.dbPath);
    const index = db.getIndex();

    expect(Object.keys(index.sources).length).toBe(0);
    expect(Object.keys(index.items).length).toBe(0);
    expect(Object.keys(index.journalists).length).toBe(0);

    db.close();
  }, 10000);

  it("should successfully log in with valid credentials", async () => {
    // Navigate back to sign-in page
    await context.page.getByTestId("signin-form-button").click();
    await context.page.waitForLoadState("networkidle", { timeout: 5000 });

    // Log in with test credentials
    await context.login();
  }, 10000);

  it("should verify logged-in journalist from Redux state", async () => {
    // Verify journalist info from Redux state
    const reduxState = await context.page.evaluate(() => {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
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
  }, 10000);

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
    const db = new DB(context.dbPath);
    const index = db.getIndex();
    firstSyncVersion = db.getVersion();

    expect(index).toEqual(EXPECTED_INDEX);
    expect(firstSyncVersion).toBe(EXPECTED_VERSION);

    db.close();
  }, 15000);

  it("should be idempotent when syncing again", async () => {
    await context.runSync();

    // Verify sources count is still the same
    const sourceCheckboxes = context.page.locator(
      '[data-testid^="source-checkbox-"]',
    );
    const sourceCount = await sourceCheckboxes.count();
    expect(sourceCount).toBe(3);

    // Verify database version stayed the same (idempotent)
    const db = new DB(context.dbPath);
    const secondVersion = db.getVersion();
    expect(secondVersion).toBe(firstSyncVersion);
    expect(secondVersion).toBe(EXPECTED_VERSION);
    db.close();
  }, 15000);
});
