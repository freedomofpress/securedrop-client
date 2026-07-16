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

// Checks that all axe a11y tests live in the a11y.test.tsx file so that they
// can run sequentially in a single worker to avoid CI flakes.
const a11yChecks = {
  meta: {
    type: "problem" as const,
    docs: {
      description:
        "Accessibility (axe) checks must all live in src/renderer/a11y.test.tsx.",
    },
    schema: [],
    messages: {
      a11yOutsideA11yFile:
        "Accessibility checks ({{name}}) must live in  " +
        "src/renderer/a11y.test.tsx file so they all run sequentially in one " +
        "worker.",
    },
  },
  create(context: {
    filename: string;
    report: (d: {
      node: object;
      messageId: string;
      data?: Record<string, string>;
    }) => void;
  }) {
    const isA11yFile = /(^|[\\/])a11y\.test\.tsx$/.test(context.filename);
    return {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      CallExpression(node: any) {
        const name =
          node.callee.type === "Identifier" ? node.callee.name : null;
        if (
          (name === "renderAndCheckA11y" || name === "checkA11y") &&
          !isA11yFile
        ) {
          context.report({
            node,
            messageId: "a11yOutsideA11yFile",
            data: { name },
          });
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
  // Keep all accessibility (axe) checks in the single consolidated
  // a11y.test.tsx file: require them there, forbid them elsewhere.
  {
    files: ["src/renderer/**/*.test.ts", "src/renderer/**/*.test.tsx"],
    plugins: {
      local: {
        rules: {
          "a11y-checks": a11yChecks,
        },
      },
    },
    rules: {
      "local/a11y-checks": "error",
    },
  },
);
