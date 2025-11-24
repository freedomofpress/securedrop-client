/// <reference types="vite/client" />

declare const __APP_VERSION__: string;
declare const __PROXY_ORIGIN__: string;
declare const __PROXY_CMD__: string;
declare const __DEV_AUTO_LOGIN__: boolean;
declare const __VITE_NONCE__: string;

interface ImportMetaEnv {
  readonly SD_SUBMISSION_KEY_FPR: string;
  readonly GNUPGHOME: string;
}

interface ImportMeta {
  readonly env: ImportMetaEnv;
}
