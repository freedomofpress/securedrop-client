import "../Item.css";

import { memo, useEffect, useState } from "react";
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
}

function normalizeFingerprint(fingerprint: string): string {
  return fingerprint.replace(/\s/g, "").toUpperCase();
}

// Badge shown on items that were additionally encrypted by the source
// before uploading. When the inner layer was encrypted to a key other than
// the current submission key, the badge is shown in the warning color and
// the tooltip includes that key's fingerprint.
const DoubleEncryptedBadge = memo(function DoubleEncryptedBadge({
  keyFingerprint,
}: DoubleEncryptedBadgeProps) {
  const { t } = useTranslation("Item");
  const { token } = theme.useToken();
  const [currentKeyFingerprint, setCurrentKeyFingerprint] = useState<
    string | null
  >(null);

  useEffect(() => {
    let cancelled = false;
    const getFingerprint = window.electronAPI.getSubmissionKeyFingerprint;
    if (getFingerprint) {
      void getFingerprint()
        .then((fingerprint) => {
          if (!cancelled) {
            setCurrentKeyFingerprint(fingerprint);
          }
        })
        .catch((error: unknown) => {
          console.warn(`Could not get submission key fingerprint: ${error}`);
        });
    }
    return () => {
      cancelled = true;
    };
  }, []);

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
