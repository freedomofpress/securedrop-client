/// <reference types="vite/client" />

// Environment variables can be accessed in code via `import.meta.env.VITE_SOME_ENV_VAR`
// See: https://vite.dev/guide/env-and-mode
// To configure local development values for environment variables, add to run.sh
interface ImportMetaEnv {
  // localdev-only: path to locally-build securedrop-proxy binary
  readonly VITE_SD_PROXY_CMD: string;
  // securedrop-proxy VM name when running in Qubes environment
  readonly VITE_PROXY_VM_NAME: string;
  // SD_PROXY_ORIGIN env var to pass into securedrop-proxy binary
  readonly VITE_SD_PROXY_ORIGIN: string;
}

interface ImportMeta {
  readonly env: ImportMetaEnv;
}

declare const __APP_VERSION__: string;
