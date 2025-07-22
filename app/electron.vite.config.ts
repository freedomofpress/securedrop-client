import { resolve } from "path";
import { defineConfig, externalizeDepsPlugin } from "electron-vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { execSync } from "child_process";

export default defineConfig(({ command }) => {
  const isDev = command === "serve";
  console.log(`Building in ${isDev ? "development" : "production"} mode`);

  const vars = {};
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
    vars["__PROXY_ORIGIN__"] = JSON.stringify("http://localhost:8081/");
    vars["__PROXY_CMD__"] = JSON.stringify(sdProxyCmd);
  } else {
    // In production, PROXY_CMD and PROXY_VM_NAME are determined at runtime.  PROXY_ORIGIN is the responsibility of the proxy command *within* the proxy VM; setting it here has no effect.
    vars["__PROXY_VM_NAME__"] = '""'; // Empty string
    vars["__PROXY_CMD__"] = '""'; // Empty string
    vars["__PROXY_ORIGIN__"] = JSON.stringify("http://localhost:8081/");
  }

  return {
    main: {
      plugins: [externalizeDepsPlugin()],
    },
    preload: {
      plugins: [externalizeDepsPlugin()],
    },
    renderer: {
      resolve: {
        alias: {
          "@renderer": resolve("src/renderer"),
        },
      },
      plugins: [react(), tailwindcss()],
      define: {
        ...vars,
        __APP_VERSION__: JSON.stringify(process.env.npm_package_version),
      },
    },
  };
});
