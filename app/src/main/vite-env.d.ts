/// <reference types="vite/client" />

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
