-- migrate:up
-- Fix items.source_uuid to reference $.source instead of $.uuid
ALTER TABLE items DROP COLUMN source_uuid;
ALTER TABLE items ADD COLUMN source_uuid text generated always as (json_extract (data, '$.source'));
-- Recreate the index that was dropped when the column was dropped
CREATE INDEX idx_items_source_uuid on items (source_uuid);

-- migrate:down
-- Revert back to the incorrect reference
DROP INDEX IF EXISTS idx_items_source_uuid;
ALTER TABLE items DROP COLUMN source_uuid;
ALTER TABLE items ADD COLUMN source_uuid text generated always as (json_extract (data, '$.uuid'));
CREATE INDEX idx_items_source_uuid on items (source_uuid);
