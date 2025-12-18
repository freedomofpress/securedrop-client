-- migrate:up
-- Add decrypted_size column to track the actual file size after decryption
-- This allows showing the real file size to users after download completes,
-- while still showing the download size (encrypted) before downloading.
ALTER TABLE items ADD COLUMN decrypted_size INTEGER;

-- Recreate items_projected view to include decrypted_size
DROP VIEW sorted_items;
DROP VIEW items_projected;

CREATE VIEW items_projected AS
SELECT
    items.uuid,
    items.data,
    items.version,
    items.plaintext,
    items.filename,
    items.kind,
    items.is_read,
    items.last_updated,
    items.source_uuid,
    items.fetch_progress,
    items.fetch_status,
    items.fetch_last_updated_at,
    items.fetch_retry_attempts,
    items.interaction_count,
    items.decrypted_size
FROM
    items
    -- project ItemDeleted event
WHERE
    NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.item_uuid = items.uuid
            AND pending_events.type = 'item_deleted'
    )
    -- project SourceDeleted, SourceConversationDeleted event
    AND NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = items.source_uuid
            AND pending_events.type IN ('source_deleted', 'source_conversation_deleted')
    )
    -- project ReplySent event
UNION ALL
SELECT
    json_extract (pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract (pending_events.data, '$.metadata') as data,
    NULL as version,
    json_extract (pending_events.data, '$.plaintext') AS plaintext,
    NULL as filename,
    'reply' AS kind,
    NULL as is_read,
    NULL as last_updated,
    json_extract (pending_events.data, '$.metadata.source') AS source_uuid,
    NULL as fetch_progress,
    NULL as fetch_status,
    NULL as fetch_last_updated_at,
    NULL as fetch_retry_attempts,
    json_extract (
        pending_events.data,
        '$.metadata.interaction_count'
    ) AS interaction_count,
    NULL as decrypted_size
FROM
    pending_events
WHERE
    pending_events.type = 'reply_sent'
    -- Check that there is no later overriding deletion
    AND NOT EXISTS (
        SELECT
            1
        FROM
            pending_events later
        WHERE
            (
                -- SourceDeleted or SourceConversationDeleted
                (
                    later.source_uuid = json_extract (pending_events.data, '$.metadata.source')
                    AND later.type IN ('source_deleted', 'source_conversation_deleted')
                )
                OR
                -- ItemDeleted
                (
                    later.item_uuid = json_extract (pending_events.data, '$.metadata.uuid')
                    AND later.type = 'item_deleted'
                )
            )
            AND later.snowflake_id > pending_events.snowflake_id
    );

-- Recreate sorted_items view
CREATE VIEW
    sorted_items AS
SELECT
    *,
    ROW_NUMBER() OVER (
        PARTITION BY
            source_uuid
        ORDER BY
            interaction_count DESC
    ) AS rn
FROM
    items_projected;

-- migrate:down
DROP VIEW sorted_items;
DROP VIEW items_projected;

CREATE VIEW items_projected AS
SELECT
    items.uuid,
    items.data,
    items.version,
    items.plaintext,
    items.filename,
    items.kind,
    items.is_read,
    items.last_updated,
    items.source_uuid,
    items.fetch_progress,
    items.fetch_status,
    items.fetch_last_updated_at,
    items.fetch_retry_attempts,
    items.interaction_count
FROM
    items
WHERE
    NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.item_uuid = items.uuid
            AND pending_events.type = 'item_deleted'
    )
    AND NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = items.source_uuid
            AND pending_events.type IN ('source_deleted', 'source_conversation_deleted')
    )
UNION ALL
SELECT
    json_extract (pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract (pending_events.data, '$.metadata') as data,
    NULL as version,
    json_extract (pending_events.data, '$.plaintext') AS plaintext,
    NULL as filename,
    'reply' AS kind,
    NULL as is_read,
    NULL as last_updated,
    json_extract (pending_events.data, '$.metadata.source') AS source_uuid,
    NULL as fetch_progress,
    NULL as fetch_status,
    NULL as fetch_last_updated_at,
    NULL as fetch_retry_attempts,
    json_extract (
        pending_events.data,
        '$.metadata.interaction_count'
    ) AS interaction_count
FROM
    pending_events
WHERE
    pending_events.type = 'reply_sent'
    AND NOT EXISTS (
        SELECT
            1
        FROM
            pending_events later
        WHERE
            (
                (
                    later.source_uuid = json_extract (pending_events.data, '$.metadata.source')
                    AND later.type IN ('source_deleted', 'source_conversation_deleted')
                )
                OR
                (
                    later.item_uuid = json_extract (pending_events.data, '$.metadata.uuid')
                    AND later.type = 'item_deleted'
                )
            )
            AND later.snowflake_id > pending_events.snowflake_id
    );

CREATE VIEW
    sorted_items AS
SELECT
    *,
    ROW_NUMBER() OVER (
        PARTITION BY
            source_uuid
        ORDER BY
            interaction_count DESC
    ) AS rn
FROM
    items_projected;

ALTER TABLE items DROP COLUMN decrypted_size;
