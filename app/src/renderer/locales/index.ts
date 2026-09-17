import en from "./en.json";
import enXA from "./en-XA.json";
import fr from "./fr.json";
import { toPseudoRtl } from "./pseudoRtl";

// Pseudolocale that lays out English RTL for testing
// Run to test RTL in dev with LANG=en_XB.UTF-8
export const PSEUDO_RTL_LANGUAGE = "en-XB";

export const resources = {
  en,
  "en-XA": enXA,
  [PSEUDO_RTL_LANGUAGE]: toPseudoRtl(en),
  fr,
} as const;
