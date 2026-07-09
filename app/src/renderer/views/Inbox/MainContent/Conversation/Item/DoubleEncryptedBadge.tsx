import "../Item.css";

import { memo } from "react";
import { useTranslation } from "react-i18next";
import { LockKeyhole, TriangleAlert } from "lucide-react";
import { Tooltip, theme } from "antd";

// Format a hex fingerprint into GPG's conventional 4-character groups
function formatFingerprint(fingerprint: string): string {
  return fingerprint.replace(/(.{4})(?=.)/g, "$1 ");
}

interface DoubleEncryptedBadgeProps {
  // Fingerprint of the key that decrypted the inner layer, when it was NOT
  // the submission key current at decryption time (e.g. a rotated key still
  // in the keyring); null in the expected case
  keyFingerprint: string | null;
}

// Badge shown on items that were additionally encrypted by the source
// before uploading. When the inner layer was encrypted to a key other than
// the current submission key, the badge is shown in the error color and the
// tooltip includes that key's fingerprint.
const DoubleEncryptedBadge = memo(function DoubleEncryptedBadge({
  keyFingerprint,
}: DoubleEncryptedBadgeProps) {
  const { t } = useTranslation("Item");
  const { token } = theme.useToken();

  if (keyFingerprint) {
    return (
      <Tooltip
        title={t("doubleEncryptedOtherKeyTooltip", {
          fingerprint: formatFingerprint(keyFingerprint),
        })}
      >
        <span
          className="double-encrypted-badge"
          style={{ color: token.colorError }}
        >
          <TriangleAlert size={12} /> {t("doubleEncryptedBadge")}
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
