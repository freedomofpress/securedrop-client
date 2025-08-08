-- migrate:up
ALTER TABLE items
ADD COLUMN source_uuid text generated always as (json_extract (data, '$.uuid'));

-- SQLite doesn't support adding fkey constraints to an existing table

-- migrate:down
ALTER TABLE items DROP COLUMN source_uuid;

