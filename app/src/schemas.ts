/**
 * Zod schemas for validating server responses
 */

import { z } from "zod";

export const UUIDSchema = z.uuid({ version: "v4" });

// Response from /api/v1/token
export const TokenResponseSchema = z.object({
  expiration: z.string(),
  token: z.string().min(1),
  journalist_uuid: UUIDSchema,
  journalist_first_name: z.nullable(z.string()),
  journalist_last_name: z.nullable(z.string()),
});

export const SourceMetadataSchema = z.object({
  uuid: UUIDSchema,
  journalist_designation: z
    .string()
    .regex(
      /^[a-z'-]+ [a-z'-]+$/,
      "Journalist designation must be two words (lowercase letters, hyphens, or apostrophes only) separated by a single space",
    ),
  is_starred: z.boolean(),
  is_seen: z.boolean(),
  has_attachment: z.boolean(),
  last_updated: z.string(),
  public_key: z.string(),
  fingerprint: z.string(),
});

export const ReplyMetadataSchema = z.object({
  kind: z.literal("reply"),
  uuid: UUIDSchema,
  source: UUIDSchema,
  size: z.number(),
  journalist_uuid: UUIDSchema,
  is_deleted_by_source: z.boolean(),
  seen_by: z.array(UUIDSchema),
  interaction_count: z.number(),
});

export const SubmissionMetadataSchema = z.object({
  kind: z.enum(["file", "message"]),
  uuid: UUIDSchema,
  source: UUIDSchema,
  size: z.number(),
  is_read: z.boolean(),
  seen_by: z.array(UUIDSchema),
  interaction_count: z.number(),
});

// Item metadata is either a reply or submission
export const ItemMetadataSchema = z.union([
  ReplyMetadataSchema,
  SubmissionMetadataSchema,
]);

export const JournalistMetadataSchema = z.object({
  uuid: UUIDSchema,
  username: z.string(),
  first_name: z.string().nullable(),
  last_name: z.string().nullable(),
});

// Index, maps UUIDs to version strings
export const IndexSchema = z.object({
  sources: z.record(UUIDSchema, z.string()),
  items: z.record(UUIDSchema, z.string()),
  journalists: z.record(UUIDSchema, z.string()),
});

// Metadata, maps UUIDs to full metadata objects
export const BatchResponseSchema = z.object({
  sources: z.record(UUIDSchema, SourceMetadataSchema),
  items: z.record(UUIDSchema, ItemMetadataSchema),
  journalists: z.record(UUIDSchema, JournalistMetadataSchema),
  events: z.record(z.string(), z.tuple([z.number(), z.string()])),
});

// Export types inferred from schemas
export type TokenResponse = z.infer<typeof TokenResponseSchema>;
export type Index = z.infer<typeof IndexSchema>;
export type BatchResponse = z.infer<typeof BatchResponseSchema>;
export type SourceMetadata = z.infer<typeof SourceMetadataSchema>;
export type ItemMetadata = z.infer<typeof ItemMetadataSchema>;
export type ReplyMetadata = z.infer<typeof ReplyMetadataSchema>;
export type SubmissionMetadata = z.infer<typeof SubmissionMetadataSchema>;
export type JournalistMetadata = z.infer<typeof JournalistMetadataSchema>;
