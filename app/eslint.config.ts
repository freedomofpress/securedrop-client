import globals, { node } from "globals";
import eslint from "@eslint/js";
import tseslint from "typescript-eslint";
import reactHooks from "eslint-plugin-react-hooks";
import reactRefresh from "eslint-plugin-react-refresh";
import eslintConfigPrettier from "eslint-config-prettier/flat";
import importPlugin from "eslint-plugin-import";
import i18next from "eslint-plugin-i18next";

export default tseslint.config(
  {
    ignores: [
      "eslint.config.ts",
      "vitest.config.ts",
      "out/**/*",
      "coverage/**/*",
    ],
  },
  {
    extends: [
      eslint.configs.recommended,
      tseslint.configs.recommended,
      importPlugin.flatConfigs.recommended,
      reactHooks.configs["recommended-latest"],
      reactRefresh.configs.recommended,
      eslintConfigPrettier,
      i18next.configs["flat/recommended"],
    ],
    files: ["**/*.ts", "**/*.tsx"],
    languageOptions: {
      globals: {
        ...globals.browser,
        ...globals.node,
      },
      parserOptions: {
        projectService: true,
      },
    },
    rules: {
      "@typescript-eslint/no-unused-vars": [
        "error",
        {
          argsIgnorePattern: "^_",
          varsIgnorePattern: "^_",
          caughtErrorsIgnorePattern: "^_",
        },
      ],
    },
    settings: {
      "import/resolver": {
        typescript: {
          alwaysTryTypes: true,
          project: "tsconfig.json",
        },
        node: {
          extensions: [".js", ".jsx", ".ts", ".tsx"],
        },
      },
    },
  },
  {
    files: [
      "**/*.test.ts",
      "**/*.test.tsx",
      "tests/**/*",
      "integration_tests/**/*",
      "**/test-component-setup.tsx",
    ],
    rules: {
      "@typescript-eslint/no-explicit-any": "off",
    },
  },
);
