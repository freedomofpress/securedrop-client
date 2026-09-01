import { useEffect, useState } from "react";

/**
 * Whether the in-development sync sidebar should be rendered, per the
 * SYNC_SIDEBAR feature flag. Defaults to disabled until the flag has been
 * read, so the panel never flashes into view on a stock configuration.
 */
export function useSyncSidebarEnabled(): boolean {
  const [enabled, setEnabled] = useState(false);

  useEffect(() => {
    let cancelled = false;
    void window.electronAPI
      .getSyncSidebarEnabled()
      .then((value) => {
        if (!cancelled) {
          setEnabled(value);
        }
      })
      .catch((error: unknown) => {
        console.warn(`Could not get sync sidebar feature flag: ${error}`);
      });

    return () => {
      cancelled = true;
    };
  }, []);

  return enabled;
}
