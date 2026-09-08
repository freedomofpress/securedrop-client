import { describe, it, expect, afterAll } from "vitest";

import i18n, { directionFor, textDirection } from "./i18n";
import { PSEUDO_RTL_LANGUAGE } from "./locales";

const bootAs = (language: string) => i18n.changeLanguage(language);

describe("i18n document direction", () => {
  afterAll(async () => {
    await bootAs("en");
  });

  it("marks the document left-to-right for the default language", () => {
    expect(document.documentElement.dir).toBe("ltr");
    expect(document.documentElement.lang).toBe("en");
  });

  it("resolves direction from the language part of a regional locale", () => {
    expect(directionFor("ar-EG")).toBe("rtl");
    expect(directionFor("fr-FR")).toBe("ltr");
  });

  it("treats the RTL pseudolocale as right-to-left", async () => {
    // i18next would derive "ltr" from this locale's "en" language subtag.
    expect(directionFor(PSEUDO_RTL_LANGUAGE)).toBe("rtl");

    await bootAs(PSEUDO_RTL_LANGUAGE);

    expect(i18n.t("common:yesterday")).toContain("\u202B");
  });

  it("keeps the accented pseudolocale left-to-right", async () => {
    await bootAs("en-XA");

    expect(directionFor("en-XA")).toBe("ltr");
    expect(i18n.t("Sidebar:sourcelist.sort.tooltip")).toContain("[!");
  });
});

describe("textDirection", () => {
  afterAll(async () => {
    await bootAs("en");
  });

  it("reports the direction of the language the app booted with", async () => {
    await bootAs("en");
    expect(textDirection()).toBe("ltr");

    await bootAs("ar");
    expect(textDirection()).toBe("rtl");
  });

  it("reports right-to-left for the RTL pseudolocale", async () => {
    await bootAs(PSEUDO_RTL_LANGUAGE);
    expect(textDirection()).toBe("rtl");
  });
});
