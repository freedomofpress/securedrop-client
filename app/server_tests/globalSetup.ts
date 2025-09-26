import type { TestProject } from "vitest/node";
import { execSync } from "child_process";
import { TOTP } from "otpauth";
import { proxyJSONRequestInner } from "../src/main/proxy";
import { ms, TokenResponse } from "../src/types";

export async function setup(project: TestProject) {
  // Note: Proxy building is handled by vitest.config.ts, but we still need to get
  // the path for this globalSetup phase since defines aren't available yet
  const stdout = execSync("cargo metadata --format-version 1")
    .toString()
    .trim();
  const targetDir = JSON.parse(stdout)["target_directory"];
  const proxyCommand = {
    command: `${targetDir}/debug/securedrop-proxy`,
    options: [],
    env: new Map([
      ["SD_PROXY_ORIGIN", "http://127.0.0.1:8081"],
      ["DISABLE_TOR", "yes"],
    ]),
    timeout: 1000 as ms,
  };

  const result = await proxyJSONRequestInner(
    {
      method: "POST",
      path_query: "/api/v1/token",
      body: JSON.stringify({
        username: "journalist",
        passphrase: "correct horse battery staple profanity oil chewy",
        one_time_code: new TOTP({
          secret: "JHCOGO7VCER3EJ4L",
        }).generate(),
      }),
      headers: {},
    },
    proxyCommand,
  );

  if (result.status !== 200) {
    throw new Error(`Failed to get token: ${JSON.stringify(result, null, 2)}`);
  }

  const token = (result.data as TokenResponse).token;
  const authHeader = `Token ${token}`;

  project.provide("token", token);
  project.provide("authHeader", authHeader);
}

declare module "vitest" {
  export interface ProvidedContext {
    token: string;
    authHeader: string;
  }
}
