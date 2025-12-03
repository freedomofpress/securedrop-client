#!/usr/bin/env node

import TranslationScreenshotAPI from "./lib.js";

async function signin(api) {
  api.context("SignIn");

  await api.reload(); // fresh state
  await api.navigate("#/signin");
  await api.takeScreenshots();

  // field required validation messages
  await api.getByTestId("sign-in-button").click();
  await api.takeScreenshots();

  await api.reload(); // to reset form state

  // field too short validation messages
  await api.getByTestId("username-input").setValue("a");
  await api.getByTestId("passphrase-input").setValue("a");
  await api.getByTestId("one-time-code-input").setValue("1");
  await api.getByTestId("sign-in-button").click();
  await api.takeScreenshots();
}

async function offlineMode(api) {
  // enter offline mode
  await api.reload();
  await api.getByTestId("use-offline-button").click();

  // get the empty state message
  api.context("MainContent");
  await api.takeScreenshots();

  // sidebar messages
  api.context("Sidebar");
  await api.takeScreenshots();

  // filter dropdown
  await api.getByTestId("filter-dropdown").click();
  await api.takeScreenshots();

  // sort tooltip
  await api.getByTestId("sort-button").hover();
  await api.takeScreenshots();

  // toggle star tooltip
  await api.getByTestId("star-button-*").hover();
  await api.takeScreenshots();

  // select all operations
  await api.getByTestId("select-all-checkbox").click();
  await api.getByTestId("bulk-delete-button").hover();
  await api.takeScreenshots();
}

async function main() {
  const api = new TranslationScreenshotAPI();

  try {
    await api.launch();
    await signin(api);
    await offlineMode(api);
  } finally {
    api.printFinalReport();
    await api.close();
  }
}

// ESM equivalent of require.main === module
if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((error) => {
    console.error(error);
    process.exit(1);
  });
}
