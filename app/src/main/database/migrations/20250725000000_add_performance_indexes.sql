-- migrate:up
-- Add generated columns for performance and to simplify queries

-- Add generated columns for sources table
ALTER TABLE sources
ADD COLUMN is_seen integer generated always as (json_extract (data, '$.is_seen')) stored;

ALTER TABLE sources
ADD COLUMN has_attachment integer generated always as (json_extract (data, '$.has_attachment')) stored;

ALTER TABLE sources
ADD COLUMN show_message_preview integer default 0;

ALTER TABLE sources
ADD COLUMN message_preview text;

-- Add generated columns for items table (in addition to the existing source_uuid)
ALTER TABLE items
ADD COLUMN kind text generated always as (json_extract (data, '$.kind')) stored;

ALTER TABLE items
ADD COLUMN is_read integer generated always as (json_extract (data, '$.is_read')) stored;

ALTER TABLE items
ADD COLUMN last_updated integer generated always as (json_extract (data, '$.last_updated')) stored;

-- Create performance indexes
CREATE INDEX idx_items_kind on items (kind);
CREATE INDEX idx_items_is_read on items (is_read);
CREATE INDEX idx_items_last_updated on items (last_updated);
CREATE INDEX idx_sources_uuid on sources (uuid);

-- migrate:down
-- Remove indexes
DROP INDEX IF EXISTS idx_items_kind;
DROP INDEX IF EXISTS idx_items_is_read;
DROP INDEX IF EXISTS idx_items_last_updated;
DROP INDEX IF EXISTS idx_sources_uuid;

-- Remove generated columns
ALTER TABLE sources DROP COLUMN is_seen;
ALTER TABLE sources DROP COLUMN has_attachment;
ALTER TABLE sources DROP COLUMN show_message_preview;
ALTER TABLE sources DROP COLUMN message_preview;
ALTER TABLE items DROP COLUMN kind;
ALTER TABLE items DROP COLUMN is_read;
ALTER TABLE items DROP COLUMN last_updated;
