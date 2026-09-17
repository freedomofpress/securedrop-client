import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, it, expect } from "vitest";

import { PSEUDO_RTL_LANGUAGE, resources } from "./index";
import { toPseudoRtl } from "./pseudoRtl";
import { normalizeLocale } from "../utils";

const localesDir = join(process.cwd(), "src/renderer/locales");

const UNREGISTERED_LOCALES = ["de", "es", "nb-NO"];

const PLURAL_SUFFIX = /_(zero|one|two|few|many|other)$/;

type Translations = { [key: string]: string | Translations };

const flatten = (translations: Translations, prefix = ""): string[] =>
  Object.entries(translations).flatMap(([key, value]) =>
    typeof value === "string"
      ? [`${prefix}${key}`]
      : flatten(value, `${prefix}${key}.`),
  );

const localeFiles = readdirSync(localesDir)
  .filter((file) => file.endsWith(".json"))
  .map((file) => file.replace(/\.json$/, ""));

const readLocale = (locale: string): Translations =>
  JSON.parse(readFileSync(join(localesDir, `${locale}.json`), "utf-8"));

const sourceKeys = new Set(flatten(readLocale("en")));

const pluralisedSourceKeys = new Set(
  [...sourceKeys]
    .filter((key) => PLURAL_SUFFIX.test(key))
    .map((key) => key.replace(PLURAL_SUFFIX, "")),
);

describe("locale registry", () => {
  it("has locale files to check", () => {
    expect(localeFiles).toContain("en");
    expect(sourceKeys.size).toBeGreaterThan(0);
  });

  it("registers every locale file, or lists it as deliberately unregistered", () => {
    const registered = Object.keys(resources);
    const unaccountedFor = localeFiles.filter(
      (locale) =>
        !registered.includes(locale) && !UNREGISTERED_LOCALES.includes(locale),
    );

    expect(unaccountedFor).toEqual([]);
  });

  it("does not list locales that no longer exist", () => {
    const missingFiles = UNREGISTERED_LOCALES.filter(
      (locale) => !localeFiles.includes(locale),
    );

    expect(missingFiles).toEqual([]);
  });

  it("keys the registry by the language tags the app resolves to", () => {
    for (const tag of Object.keys(resources)) {
      expect(normalizeLocale(tag), `resources["${tag}"]`).toBe(tag);
    }
  });

  it("generates the RTL pseudolocale from the full set of source strings", () => {
    const pseudoKeys = flatten(resources[PSEUDO_RTL_LANGUAGE]);

    expect(new Set(pseudoKeys)).toEqual(sourceKeys);
  });

  it.each(localeFiles.filter((locale) => locale !== "en"))(
    "%s has no keys the English source doesn't have",
    (locale) => {
      const unknownKeys = flatten(readLocale(locale)).filter((key) => {
        const baseKey = key.replace(PLURAL_SUFFIX, "");
        return !sourceKeys.has(key) && !pluralisedSourceKeys.has(baseKey);
      });

      expect(unknownKeys).toEqual([]);
    },
  );
});

describe("RTL pseudolocale", () => {
  it("wraps strings in a right-to-left embedding, preserving placeholders", () => {
    const pseudo = toPseudoRtl({
      plain: "Delete Account",
      interpolated: "Delete {{count}} accounts",
      markup: "<bold>Select a source</bold> from the list.",
      nested: { deep: "Yesterday" },
      empty: "",
    });

    expect(pseudo.plain).toBe("\u202B[Delete Account]\u202C");
    expect(pseudo.interpolated).toBe("\u202B[Delete {{count}} accounts]\u202C");
    expect(pseudo.markup).toBe(
      "\u202B[<bold>Select a source</bold> from the list.]\u202C",
    );
    expect(pseudo.nested.deep).toBe("\u202B[Yesterday]\u202C");
    // Wrapping an empty string would turn it into visible "[]" brackets.
    expect(pseudo.empty).toBe("");
  });

  it("leaves the English source strings untouched", () => {
    expect(resources.en.common.yesterday).toBe("Yesterday");
    expect(resources[PSEUDO_RTL_LANGUAGE].common.yesterday).not.toBe(
      resources.en.common.yesterday,
    );
  });
});
