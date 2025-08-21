-- migrate:up
ALTER TABLE items
ADD COLUMN fetch_progress INTEGER;

ALTER TABLE items
ADD COLUMN fetch_status INTEGER NOT NULL DEFAULT 0;

ALTER TABLE items 
ADD COLUMN fetch_last_updated_at timestamp;

ALTER TABLE items 
ADD COLUMN fetch_retry_attempts integer NOT NULL DEFAULT 0;

CREATE INDEX idx_items_fetch_status ON items (fetch_status);

-- migrate:down

DROP INDEX IF EXISTS idx_items_fetch_status;

ALTER TABLE items DROP COLUMN fetch_progress;
ALTER TABLE items DROP COLUMN fetch_status;
ALTER TABLE items DROP COLUMN fetch_last_updated_at;
ALTER TABLE items DROP COLUMN fetch_retry_attempts;
