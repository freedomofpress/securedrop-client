-- migrate:up
-- Track retry attempts and the latest server status for each pending event.
-- Allows us to de-prioritize previously-failed events when scheduling sync 
-- batches, and exclude events that have already been reported + accepted by
-- the server (EventStatus.AlreadyReported).
ALTER TABLE pending_events
ADD COLUMN retry_attempts INTEGER NOT NULL DEFAULT 0;
ALTER TABLE pending_events
ADD COLUMN last_event_status INTEGER;
-- migrate:down
ALTER TABLE pending_events
DROP COLUMN last_event_status;
ALTER TABLE pending_events
DROP COLUMN retry_attempts;