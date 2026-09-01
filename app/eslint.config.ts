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
    // Keep this regex in sync with src/renderer/a11y.test.tsx
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

// Tailwind utilities that hard-code a physical side, mapped to the logical
// utility that mirrors automatically in right-to-left languages.
const PHYSICAL_UTILITIES: Record<string, string> = {
  ml: "ms-*",
  mr: "me-*",
  pl: "ps-*",
  pr: "pe-*",
  left: "start-*",
  right: "end-*",
  "border-l": "border-s-*",
  "border-r": "border-e-*",
  "rounded-l": "rounded-s-*",
  "rounded-r": "rounded-e-*",
  "rounded-tl": "rounded-ss-*",
  "rounded-tr": "rounded-se-*",
  "rounded-bl": "rounded-es-*",
  "rounded-br": "rounded-ee-*",
  "scroll-ml": "scroll-ms-*",
  "scroll-mr": "scroll-me-*",
  "scroll-pl": "scroll-ps-*",
  "scroll-pr": "scroll-pe-*",
  "text-left": "text-start",
  "text-right": "text-end",
  "float-left": "float-start",
  "float-right": "float-end",
  "clear-left": "clear-start",
  "clear-right": "clear-end",
};

// The same, for inline `style` props.
const PHYSICAL_STYLE_PROPERTIES: Record<string, string> = {
  marginLeft: "marginInlineStart",
  marginRight: "marginInlineEnd",
  paddingLeft: "paddingInlineStart",
  paddingRight: "paddingInlineEnd",
  borderLeft: "borderInlineStart",
  borderRight: "borderInlineEnd",
  borderLeftWidth: "borderInlineStartWidth",
  borderRightWidth: "borderInlineEndWidth",
  borderLeftColor: "borderInlineStartColor",
  borderRightColor: "borderInlineEndColor",
  borderLeftStyle: "borderInlineStartStyle",
  borderRightStyle: "borderInlineEndStyle",
  borderTopLeftRadius: "borderStartStartRadius",
  borderTopRightRadius: "borderStartEndRadius",
  borderBottomLeftRadius: "borderEndStartRadius",
  borderBottomRightRadius: "borderEndEndRadius",
  left: "insetInlineStart",
  right: "insetInlineEnd",
};

// `textAlign: "left"` and `float: "right"` need the value mirrored, not the key.
const PHYSICAL_STYLE_VALUES: Record<string, string> = {
  left: "start",
  right: "end",
};

// Finds the physical utilities in a `className` string. Tailwind variant
// prefixes ("hover:", "md:"), the negative sign and the "!" important marker
// are stripped so only the utility itself is matched.
const physicalUtilitiesIn = (classes: string) => {
  const hits: { token: string; logical: string }[] = [];
  for (const token of classes.split(/\s+/).filter(Boolean)) {
    const variants = token.split(":");
    const utility = (variants[variants.length - 1] ?? "")
      .replace(/^[-!]+/, "")
      .replace(/!$/, "");
    const physical = Object.keys(PHYSICAL_UTILITIES).find(
      (candidate) =>
        utility === candidate || utility.startsWith(`${candidate}-`),
    );
    if (physical) {
      hits.push({ token, logical: PHYSICAL_UTILITIES[physical] });
    }
  }
  return hits;
};

// Requires CSS logical properties so that layouts mirror for right-to-left
// languages instead of needing a second set of RTL-only overrides.
const logicalCss = {
  meta: {
    type: "problem" as const,
    docs: {
      description:
        "Use CSS logical properties instead of physical (left/right) ones " +
        "so layouts mirror in right-to-left languages.",
    },
    schema: [],
    messages: {
      physicalUtility:
        'Physical Tailwind utility "{{token}}": use "{{logical}}" instead ' +
        "so the layout mirrors in right-to-left languages.",
      physicalStyleProperty:
        'Physical style property "{{property}}": use "{{logical}}" instead ' +
        "so the layout mirrors in right-to-left languages.",
      physicalStyleValue:
        'Physical "{{property}}" value "{{value}}": use "{{logical}}" ' +
        "instead so the layout mirrors in right-to-left languages.",
    },
  },
  create(context: {
    report: (d: {
      node: object;
      messageId: string;
      data?: Record<string, string>;
    }) => void;
  }) {
    /* eslint-disable @typescript-eslint/no-explicit-any */
    const reportClasses = (node: any, classes: string) => {
      for (const { token, logical } of physicalUtilitiesIn(classes)) {
        context.report({
          node,
          messageId: "physicalUtility",
          data: { token, logical },
        });
      }
    };

    return {
      // Any string inside a className attribute is a class list, including
      // those in template literals, ternaries and clsx()-style helpers.
      "JSXAttribute[name.name='className'] Literal"(node: any) {
        if (typeof node.value === "string") {
          reportClasses(node, node.value);
        }
      },
      "JSXAttribute[name.name='className'] TemplateElement"(node: any) {
        reportClasses(node, node.value?.raw ?? "");
      },
      "JSXAttribute[name.name='style'] Property"(node: any) {
        const property =
          node.key?.type === "Identifier" ? node.key.name : node.key?.value;
        if (typeof property !== "string") {
          return;
        }
        const logical = PHYSICAL_STYLE_PROPERTIES[property];
        if (logical) {
          context.report({
            node,
            messageId: "physicalStyleProperty",
            data: { property, logical },
          });
          return;
        }
        const value = node.value?.value;
        if (
          (property === "textAlign" || property === "float") &&
          typeof value === "string" &&
          PHYSICAL_STYLE_VALUES[value]
        ) {
          context.report({
            node,
            messageId: "physicalStyleValue",
            data: { property, value, logical: PHYSICAL_STYLE_VALUES[value] },
          });
        }
      },
    };
    /* eslint-enable @typescript-eslint/no-explicit-any */
  },
};

// ---------------------------------------------------------------------------

const openExternalMessage =
  "shell.openExternal() is banned: it launches a URL in the host desktop's " +
  "default handler.";

// Ant Design placements are physical and, unlike CSS logical properties, are
// not mirrored for right-to-left languages.
const placementMessage =
  "Horizontal Ant Design placements are not mirrored for right-to-left " +
  "languages: wrap this in mirrorPlacement(placement, direction) from " +
  "src/renderer/utils.ts.";

const horizontalPlacement =
  "/^(left|right|leftTop|leftBottom|rightTop|rightBottom|topLeft|topRight|bottomLeft|bottomRight)$/";

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
    plugins: {
      local: {
        rules: {
          "a11y-checks": a11yChecks,
          "logical-css": logicalCss,
        },
      },
    },
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
      "local/logical-css": "error",
      // Forbid electron's shell.openExternal()
      "no-restricted-syntax": [
        "error",
        {
          selector: "MemberExpression[property.name='openExternal']",
          message: openExternalMessage,
        },
        {
          selector: "ImportSpecifier[imported.name='openExternal']",
          message: openExternalMessage,
        },
        {
          selector:
            "ObjectPattern > Property[key.name='openExternal'][computed=false]",
          message: openExternalMessage,
        },
        {
          selector: "MemberExpression[property.value='openExternal']",
          message: openExternalMessage,
        },
        // // Require mirrorPlacement() for horizontal antd placements
        {
          selector: `JSXAttribute[name.name='placement'] > Literal[value=${horizontalPlacement}]`,
          message: placementMessage,
        },
        {
          selector: `JSXAttribute[name.name='placement'] > JSXExpressionContainer > Literal[value=${horizontalPlacement}]`,
          message: placementMessage,
        },
      ],
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
    rules: {
      "local/a11y-checks": "error",
    },
  },
);
