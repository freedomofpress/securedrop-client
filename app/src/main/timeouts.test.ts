import { describe, it, expect } from "vitest";
import { z } from "zod";
import { bytes, ms } from "../types";
import { IndexSchema, BatchResponseSchema } from "../schemas";
import { DEFAULT_PROXY_CMD_TIMEOUT_MS } from "./proxy";
import { getRealisticTimeout, estimateSize, estimateTimeout } from "./timeouts";

describe("getRealisticTimeout", () => {
  it("returns the floor for zero-size requests", () => {
    const timeout = getRealisticTimeout(0 as bytes);
    expect(timeout).toBe(25_000);
  });

  it("returns the floor for zero-size requests with custom floor", () => {
    const timeout = getRealisticTimeout(0 as bytes, 10_000 as ms);
    expect(timeout).toBe(10_000);
  });

  it("scales with size", () => {
    const small = getRealisticTimeout(1_000 as bytes);
    const large = getRealisticTimeout(100_000 as bytes);
    expect(large).toBeGreaterThan(small);
  });

  it("always returns at least the floor", () => {
    const timeout = getRealisticTimeout(1 as bytes);
    expect(timeout).toBeGreaterThanOrEqual(25_000);
  });

  it("calculates correctly for 1 MiB", () => {
    // 1 MiB = 1,048,576 bytes
    // (1048576 / 50000) * 1.5 * 1000 = 31457.28 → ceil = 31458
    // 31458 + 25000 = 56458
    const timeout = getRealisticTimeout(1_048_576 as bytes);
    expect(timeout).toBe(56_458);
  });
});

describe("estimateSize", () => {
  it("estimates IndexSchema size based on record count", () => {
    const size = estimateSize(IndexSchema, 100);
    // IndexSchema recordSize is 106
    expect(size).toBe(10_600);
  });

  it("estimates BatchResponseSchema size based on record count", () => {
    const size = estimateSize(BatchResponseSchema, 50);
    // BatchResponseSchema recordSize is 1000
    expect(size).toBe(50_000);
  });

  it("returns zero for zero records", () => {
    const size = estimateSize(IndexSchema, 0);
    expect(size).toBe(0);
  });

  it("throws for unregistered schemas", () => {
    const unregistered = z.object({ foo: z.string() });
    expect(() => estimateSize(unregistered, 10)).toThrow(
      "Can't estimate size for unregistered schema",
    );
  });
});

describe("estimateTimeout", () => {
  it("returns at least DEFAULT_PROXY_CMD_TIMEOUT_MS for zero records", () => {
    const timeout = estimateTimeout(IndexSchema, 0);
    expect(timeout).toBe(DEFAULT_PROXY_CMD_TIMEOUT_MS);
  });

  it("returns at least DEFAULT_PROXY_CMD_TIMEOUT_MS when records is undefined", () => {
    const timeout = estimateTimeout(IndexSchema);
    expect(timeout).toBe(DEFAULT_PROXY_CMD_TIMEOUT_MS);
  });

  it("increases with record count", () => {
    const small = estimateTimeout(IndexSchema, 10);
    const large = estimateTimeout(IndexSchema, 10_000);
    expect(large).toBeGreaterThan(small);
  });

  it("is larger for BatchResponseSchema than IndexSchema at the same record count", () => {
    const indexTimeout = estimateTimeout(IndexSchema, 100);
    const batchTimeout = estimateTimeout(BatchResponseSchema, 100);
    expect(batchTimeout).toBeGreaterThan(indexTimeout);
  });
});
