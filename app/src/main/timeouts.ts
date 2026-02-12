import { bytes, ms } from "../types";

// Calculate a realistic timeout in milliseconds based on the size of the download.
// This scales the timeout per file so that it increases as the file size increases.
//
// Based on Tor metrics, reasonable estimations for download times over Tor:
//   50 KiB  (51200 bytes)   =  6   seconds  (8,533 bytes/second)
//   1  MiB  (1049000 bytes) =  15  seconds  (~69,905 bytes/second)
//
// For more information, see:
// https://metrics.torproject.org/torperf.html?start=2022-12-06&end=2023-03-06&server=onion
//
// The timeout returned is larger than the expected download time to account for
// network variability. We use 50,000 bytes/second instead of 69,905 bytes/second
// and apply a 1.5x adjustment factor.
//
// Minimum timeout is 25 seconds.
export function getRealisticTimeout(size: bytes): ms {
  const TIMEOUT_BYTES_PER_SECOND = 50_000.0;
  const TIMEOUT_ADJUSTMENT_FACTOR = 1.5;
  const TIMEOUT_BASE = 25_000; // 25 seconds in milliseconds

  const timeout = Math.ceil(
    (size / TIMEOUT_BYTES_PER_SECOND) * TIMEOUT_ADJUSTMENT_FACTOR * 1000,
  );
  return (timeout + TIMEOUT_BASE) as ms;
}
