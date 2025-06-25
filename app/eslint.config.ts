import globals, { node } from "globals";
import eslint from "@eslint/js";
import tseslint from "typescript-eslint";
import reactHooks from "eslint-plugin-react-hooks";
import reactRefresh from "eslint-plugin-react-refresh";
import eslintConfigPrettier from "eslint-config-prettier/flat";
// @ts-expect-error: No types for eslint-plugin-import
import importPlugin from "eslint-plugin-import";

export default tseslint.config({
  extends: [
    eslint.configs.recommended,
    tseslint.configs.recommended,
    importPlugin.flatConfigs.recommended,
    reactHooks.configs["recommended-latest"],
    reactRefresh.configs.recommended,
    eslintConfigPrettier,
  ],
  files: ["**/*.ts", "**/*.tsx"],
  ignores: ["eslint.config.ts", ".vite/**/*"],
  languageOptions: {
    globals: {
      ...globals.browser,
      ...globals.node,
    },
    parserOptions: {
      projectService: true,
      tsconfigRootDir: __dirname,
    },
  },
  settings: {
    "import/resolver": {
      node: {
        extensions: [".js", ".jsx", ".ts", ".tsx"],
      },
    },
  },
});
