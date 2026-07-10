-- migrate:up
-- Persist when a failed pending event becomes eligible for another attempt.
ALTER TABLE pending_events
ADD COLUMN next_retry_at INTEGER NOT NULL DEFAULT 0;

-- migrate:down
ALTER TABLE pending_events
DROP COLUMN next_retry_at;
