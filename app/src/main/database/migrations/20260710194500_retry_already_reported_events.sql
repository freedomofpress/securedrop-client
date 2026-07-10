-- migrate:up
-- Delay retries for destructive events that may still be processing on the
-- server. The recorded delay lets selection detect a backward wall-clock jump.
ALTER TABLE pending_events
ADD COLUMN next_retry_at TIMESTAMP;
ALTER TABLE pending_events
ADD COLUMN retry_delay_seconds INTEGER;

-- Release destructive events stranded by the previous permanent 208 filter.
UPDATE pending_events
SET next_retry_at = CURRENT_TIMESTAMP,
    retry_delay_seconds = 0
WHERE last_event_status = 208
  AND type IN (
    'item_deleted',
    'source_deleted',
    'source_conversation_truncated'
  );

-- migrate:down
ALTER TABLE pending_events
DROP COLUMN retry_delay_seconds;
ALTER TABLE pending_events
DROP COLUMN next_retry_at;
