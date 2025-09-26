import { execSync } from "child_process";
import { TOTP } from "otpauth";
import { proxyJSONRequestInner } from "../src/main/proxy";
import { ms, ProxyCommand, TokenResponse } from "../src/types";
import { beforeAll } from "vitest";

declare global {
  var proxyCommand: ProxyCommand;
  var token: string;
  var authHeader: string;
}

export {};

beforeAll(async () => {
  // Build sd-proxy binary
  execSync("make -C ../proxy build");
  const stdout = execSync("cargo metadata --format-version 1")
    .toString()
    .trim();
  const targetDir = JSON.parse(stdout)["target_directory"];
  globalThis.proxyCommand = {
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
    globalThis.proxyCommand,
  );
  expect(result.status).toEqual(200);
  expect(result.headers.get("content-type")).toEqual("application/json");
  globalThis.token = (result.data as TokenResponse).token;
  globalThis.authHeader = `Token ${globalThis.token}`;
}, 60000);
