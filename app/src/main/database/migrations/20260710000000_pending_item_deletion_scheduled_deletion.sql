-- migrate:up
UPDATE items
SET fetch_status = 9
WHERE uuid IN (
  SELECT item_uuid
  FROM pending_events
  WHERE type = 'item_deleted'
);

-- migrate:down
-- Previous fetch statuses cannot be reconstructed after this data migration.
