import { useEffect, useState } from "react";

export function useSubmissionKeyFingerprint(enabled = true): string | null {
  const [fingerprint, setFingerprint] = useState<string | null>(null);

  useEffect(() => {
    if (!enabled) {
      return;
    }

    let cancelled = false;
    void window.electronAPI
      .getSubmissionKeyFingerprint()
      .then((value) => {
        if (!cancelled) {
          setFingerprint(value);
        }
      })
      .catch((error: unknown) => {
        console.warn(`Could not get submission key fingerprint: ${error}`);
      });

    return () => {
      cancelled = true;
    };
  }, [enabled]);

  return fingerprint;
}
