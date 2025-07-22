import { resolve } from "path";
import { defineConfig, externalizeDepsPlugin } from "electron-vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { execSync } from "child_process";

export default defineConfig(({ command }) => {
  const isDev = command === "serve";
  console.log(`Building in ${isDev ? "development" : "production"} mode`);

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

  const vars = {};
  if (isDev) {
    // Get the absolute path to the proxy binary
    const sdProxyCmd = resolve(proxyPath);
    vars["__PROXY_ORIGIN__"] = JSON.stringify("http://localhost:8081/");
    vars["__PROXY_CMD__"] = JSON.stringify(sdProxyCmd);
  } else {
    // These are determined at runtime in production
    vars["__PROXY_ORIGIN__"] = JSON.stringify("http://localhost:8081/");
    vars["__PROXY_CMD__"] = "";
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
