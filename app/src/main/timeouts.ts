import { z } from "zod";
import { bytes, ms } from "../types";
import { registry } from "../schemas";
import { DEFAULT_PROXY_CMD_TIMEOUT_MS } from "./proxy";

// Calculate a realistic timeout in milliseconds based on the size of the total
// request (including response).  This scales the timeout per request so that it
// increases with the size.
//
// Based on Tor metrics, reasonable estimations for transfer times over Tor:
//   50 KiB  (51200 bytes)   =  6   seconds  (8,533 bytes/second)
//   1  MiB  (1049000 bytes) =  15  seconds  (~69,905 bytes/second)
//
// For more information, see:
// https://metrics.torproject.org/torperf.html?start=2022-12-06&end=2023-03-06&server=onion
//
// The timeout returned is larger than the expected transfer time to account for
// network variability. We use 50,000 bytes/second instead of 69,905 bytes/second
// and apply a 1.5x adjustment factor.
//
// Default minimum timeout (floor) is 25 seconds.
export function getRealisticTimeout(size: bytes, floor = 25_000 as ms): ms {
  const TIMEOUT_BYTES_PER_SECOND = 50_000.0;
  const TIMEOUT_ADJUSTMENT_FACTOR = 1.5;

  const timeout = Math.ceil(
    (size / TIMEOUT_BYTES_PER_SECOND) * TIMEOUT_ADJUSTMENT_FACTOR * 1000,
  );
  return (timeout + floor) as ms;
}

// Estimate the size of a request/response schema based on its expected size per
// record.  The schema MUST be registered with this metadata.
export function estimateSize(schema: z.Schema, records: number): bytes {
  const meta = registry.get(schema);
  if (!meta) {
    throw new Error("Can't estimate size for unregistered schema");
  }

  const recordSize = meta.recordSize;
  return (records * recordSize) as bytes;
}

// Estimate a timeout for a request/response schema based on its expected size
// per record.
export function estimateTimeout(schema: z.Schema, records?: number): ms {
  if (!records) {
    records = 0;
  }

  const size = estimateSize(schema, records);
  const timeout = getRealisticTimeout(size, DEFAULT_PROXY_CMD_TIMEOUT_MS);

  console.debug(
    `Expecting ${schema.description} of ${records} records to be about ${size} bytes within ${timeout} ms`,
  );
  return timeout;
}
