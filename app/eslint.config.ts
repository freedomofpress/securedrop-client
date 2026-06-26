import globals, { node } from "globals";
import eslint from "@eslint/js";
import { defineConfig } from "eslint/config";
import tseslint from "typescript-eslint";
import reactHooks from "eslint-plugin-react-hooks";
import reactRefresh from "eslint-plugin-react-refresh";
import eslintConfigPrettier from "eslint-config-prettier/flat";
import importPlugin from "eslint-plugin-import";
import i18next from "eslint-plugin-i18next";
import jsxA11y from "eslint-plugin-jsx-a11y";

// Local rule: test files that call renderWithProviders must also call
// renderAndCheckA11y so every rendered component is checked for accessibility.
const requireA11yInTests = {
  meta: {
    type: "suggestion" as const,
    docs: {
      description:
        "Test files that call renderWithProviders must also call renderAndCheckA11y.",
    },
    schema: [],
    messages: {
      missingA11yCall:
        "This test file calls renderWithProviders but never calls " +
        "renderAndCheckA11y. Add at least one renderAndCheckA11y(...) call " +
        "to verify accessibility.",
    },
  },
  create(context: { report: (d: object) => void }) {
    let usesRenderWithProviders = false;
    let usesRenderAndCheckA11y = false;
    let programNode: object | null = null;
    return {
      Program(node: object) {
        programNode = node;
      },
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      CallExpression(node: any) {
        const name =
          node.callee.type === "Identifier" ? node.callee.name : null;
        if (name === "renderWithProviders") {
          usesRenderWithProviders = true;
        }
        if (name === "renderAndCheckA11y") {
          usesRenderAndCheckA11y = true;
        }
      },
      "Program:exit"() {
        if (usesRenderWithProviders && !usesRenderAndCheckA11y) {
          context.report({ node: programNode!, messageId: "missingA11yCall" });
        }
      },
    };
  },
};

// ---------------------------------------------------------------------------

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
      reactHooks.configs.flat["recommended-latest"],
      reactRefresh.configs.recommended,
      eslintConfigPrettier,
      i18next.configs["flat/recommended"],
      jsxA11y.flatConfigs.strict,
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
      curly: ["error", "all"],
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
  // Require renderAndCheckA11y in every renderer test that calls renderWithProviders.
  {
    files: ["src/renderer/**/*.test.ts", "src/renderer/**/*.test.tsx"],
    plugins: {
      local: {
        rules: {
          "require-a11y-in-tests": requireA11yInTests,
        },
      },
    },
    rules: {
      "local/require-a11y-in-tests": "error",
    },
  },
);
