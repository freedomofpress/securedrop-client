-- migrate:up
ALTER TABLE items
ADD COLUMN source_id text;

-- SQLite doesn't support adding fkey constraints to an existing table

-- migrate:down
ALTER TABLE items DROP COLUMN source_id;

