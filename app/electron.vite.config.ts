import path, { resolve } from "path";
import { defineConfig, externalizeDepsPlugin } from "electron-vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { execSync, spawnSync } from "child_process";
import { randomBytes } from "crypto";
import fs from "fs";
import os from "os";

export default defineConfig(({ mode }) => {
  console.log(`Building in ${mode} mode`);

  // Generate Vite CSP nonce for dev mode
  const viteNonce =
    mode === "development" ? randomBytes(32).toString("base64") : "";

  const mainVars: Record<string, string> = {};
  if (mode === "development" || mode === "test") {
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
    // Load test submission key
    mainVars["import.meta.env.SD_SUBMISSION_KEY_FPR"] = JSON.stringify(
      "65A1B5FF195B56353CC63DFFCC40EF1228271441",
    );
    // Set up a temporary GPG keyring with the secret key imported
    const gpgHome = fs.mkdtempSync(
      path.join(fs.realpathSync(os.tmpdir()), "sd-app-gpg"),
    );
    const result = spawnSync("gpg", [
      "--homedir",
      gpgHome,
      "--import",
      "scripts/securedrop-test-key.asc",
    ]);
    if (result.error) {
      throw result.error;
    } else if (result.status !== 0) {
      throw new Error(
        `gpg exited with non-zero code ${result.status}: ${result.stderr}`,
      );
    }
    mainVars["import.meta.env.GNUPGHOME"] = JSON.stringify(gpgHome);
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
        __DEV_AUTO_LOGIN__: mode === "development",
      },
      build: {
        assetsInlineLimit: 0, // Disable inlining assets as data URIs for strict CSP
      },
      html:
        mode === "development"
          ? {
              cspNonce: viteNonce,
            }
          : undefined,
    },
  };
});
