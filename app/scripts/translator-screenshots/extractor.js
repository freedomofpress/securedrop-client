#!/usr/bin/env node

import { existsSync, readFileSync } from "fs";
import { join } from "path";

/**
 * Extracts translation keys and their values from locale files
 * Handles nested objects and interpolation
 */
class TranslationExtractor {
  constructor(localesPath = "./src/renderer/locales") {
    this.localesPath = localesPath;
  }

  /**
   * Load and parse locale file
   */
  loadLocale(locale = "en") {
    const filePath = join(this.localesPath, `${locale}.json`);
    if (!existsSync(filePath)) {
      throw new Error(`Locale file not found: ${filePath}`);
    }

    const content = readFileSync(filePath, "utf8");
    return JSON.parse(content);
  }

  /**
   * Flatten nested object into dot-notation keys
   * e.g., { SignIn: { title: "Sign in" } } -> { "SignIn.title": "Sign in" }
   */
  flattenObject(obj, prefix = "") {
    const flattened = {};

    for (const [key, value] of Object.entries(obj)) {
      const newKey = prefix ? `${prefix}.${key}` : key;

      if (typeof value === "object" && value !== null) {
        Object.assign(flattened, this.flattenObject(value, newKey));
      } else {
        flattened[newKey] = value;
      }
    }

    return flattened;
  }

  /**
   * Process interpolated strings (e.g., "v{{version}}" -> "v0.0.1")
   */
  processInterpolation(text, variables = {}) {
    // Default variables that might be used
    const defaultVars = {
      version: "0.0.1", // From package.json
      designation: "test-source",
      ...variables,
    };

    return text.replace(/\{\{(\w+)\}\}/g, (match, varName) => {
      return defaultVars[varName] || match;
    });
  }

  /**
   * Extract translation keys for a specific namespace
   */
  extractNamespaceKeys(namespace, locale = "en", variables = {}) {
    const localeData = this.loadLocale(locale);
    const flattened = this.flattenObject(localeData);

    const namespaceKeys = {};
    const namespacePrefix = `${namespace}.`;

    for (const [key, value] of Object.entries(flattened)) {
      if (key.startsWith(namespacePrefix)) {
        const shortKey = key.substring(namespacePrefix.length);
        const processedValue = this.processInterpolation(value, variables);

        namespaceKeys[shortKey] = {
          fullKey: key,
          originalText: value,
          processedText: processedValue,
          hasInterpolation: value.includes("{{"),
        };
      }
    }

    return namespaceKeys;
  }
}

export default TranslationExtractor;
