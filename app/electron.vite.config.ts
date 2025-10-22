import { resolve } from "path";
import { defineConfig, externalizeDepsPlugin } from "electron-vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { execSync } from "child_process";
import { randomBytes } from "crypto";

export default defineConfig(({ mode }) => {
  const isDev = mode === "development";
  console.log(`Building in ${isDev ? "development" : "production"} mode`);

  // Generate Vite CSP nonce for dev mode
  const viteNonce = isDev ? randomBytes(32).toString("base64") : "";

  const mainVars: Record<string, string> = {};
  if (isDev) {
    // Build the proxy: `make -C ../proxy build`
    try {
      console.log("Building proxy...");
      execSync("make -C ../proxy build", { stdio: "inherit" });
      console.log("Proxy build completed successfully");
    } catch (error) {
      console.error("Failed to build proxy:", error);
      process.exit(1);
    }

    // Get the path to proxy binary
    const stdout = execSync("cargo metadata --format-version 1", {
      encoding: "utf-8",
    });
    const metadata = JSON.parse(stdout);
    const targetDir = metadata.target_directory;
    const proxyPath = `${targetDir}/debug/securedrop-proxy`;

    // Get the absolute path to the proxy binary
    const sdProxyCmd = resolve(proxyPath);
    mainVars["__PROXY_ORIGIN__"] = JSON.stringify("http://localhost:8081/");
    mainVars["__PROXY_CMD__"] = JSON.stringify(sdProxyCmd);
    mainVars["__VITE_NONCE__"] = JSON.stringify(viteNonce);
  } else {
    // In production, PROXY_CMD is determined at runtime, and PROXY_ORIGIN is managed by the proxy VM
    mainVars["__PROXY_CMD__"] = '""'; // Empty string
    mainVars["__PROXY_ORIGIN__"] = '""'; // Empty string
    mainVars["__VITE_NONCE__"] = '""'; // Empty string
  }

  console.log("Using main vars:", mainVars);

  return {
    main: {
      plugins: [externalizeDepsPlugin()],
      define: mainVars,
      build: {
        sourcemap: true,
      },
    },
    preload: {
      plugins: [externalizeDepsPlugin()],
      build: {
        sourcemap: true,
      },
    },
    renderer: {
      resolve: {
        alias: {
          "@renderer": resolve("src/renderer"),
        },
      },
      plugins: [react(), tailwindcss()],
      define: {
        __APP_VERSION__: JSON.stringify(process.env.npm_package_version),
        __DEV_AUTO_LOGIN__: isDev,
      },
      build: {
        assetsInlineLimit: 0, // Disable inlining assets as data URIs for strict CSP
      },
      html: isDev
        ? {
            cspNonce: viteNonce,
          }
        : undefined,
    },
  };
});
