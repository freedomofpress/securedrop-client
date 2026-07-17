import "../Item.css";

import { memo } from "react";
import { useTranslation } from "react-i18next";
import { LockKeyhole } from "lucide-react";
import { Tooltip, theme } from "antd";

// Format a hex fingerprint into GPG's conventional 4-character groups
function formatFingerprint(fingerprint: string): string {
  return fingerprint.replace(/(.{4})(?=.)/g, "$1 ");
}

interface DoubleEncryptedBadgeProps {
  // Full primary fingerprint of the key that decrypted the inner layer.
  keyFingerprint: string;
  // Full primary fingerprint of the currently configured submission key.
  currentKeyFingerprint: string | null;
}

function normalizeFingerprint(fingerprint: string): string | null {
  const normalized = fingerprint.replace(/\s/g, "").toUpperCase();
  return /^[0-9A-F]{40}$/.test(normalized) ? normalized : null;
}

// Badge shown on items that were additionally encrypted by the source
// before uploading. When the inner layer was encrypted to a key other than
// the current submission key, the badge is shown in the warning color and
// the tooltip includes that key's fingerprint.
const DoubleEncryptedBadge = memo(function DoubleEncryptedBadge({
  keyFingerprint,
  currentKeyFingerprint,
}: DoubleEncryptedBadgeProps) {
  const { t } = useTranslation("Item");
  const { token } = theme.useToken();
  // Until configuration arrives, use the normal badge. Exact normalized
  // equality is required; short key IDs must never be treated as fingerprints.
  const isOtherKey =
    currentKeyFingerprint !== null &&
    normalizeFingerprint(keyFingerprint) !==
      normalizeFingerprint(currentKeyFingerprint);

  if (isOtherKey) {
    return (
      <Tooltip
        title={t("doubleEncryptedOtherKeyTooltip", {
          fingerprint: formatFingerprint(keyFingerprint),
        })}
      >
        <span
          className="double-encrypted-badge"
          style={{ color: token.colorWarning }}
        >
          <LockKeyhole size={12} /> {t("doubleEncryptedBadge")}
        </span>
      </Tooltip>
    );
  }

  return (
    <Tooltip title={t("doubleEncryptedTooltip")}>
      <span className="double-encrypted-badge">
        <LockKeyhole size={12} /> {t("doubleEncryptedBadge")}
      </span>
    </Tooltip>
  );
});

export default DoubleEncryptedBadge;
