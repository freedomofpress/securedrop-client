-- migrate:up
-- Keep truncation events local until their covered plaintext has been removed.
ALTER TABLE pending_events
ADD COLUMN local_cleanup_pending INTEGER NOT NULL DEFAULT 0
CHECK (local_cleanup_pending IN (0, 1));

DROP VIEW IF EXISTS items_projected;
CREATE VIEW items_projected AS
SELECT
    items.uuid,
    items.data,
    items.version,
    items.plaintext,
    items.filename,
    items.kind,
    CASE
        WHEN items.is_read THEN 1
        WHEN EXISTS (
            SELECT 1 FROM pending_events
            WHERE pending_events.item_uuid = items.uuid
                AND pending_events.type = 'item_seen'
        ) THEN 1
        WHEN EXISTS (
            SELECT 1 FROM pending_events
            WHERE pending_events.source_uuid = items.source_uuid
                AND pending_events.type = 'source_conversation_seen'
                AND CAST(json_extract(pending_events.data, '$.upper_bound') AS INTEGER) >= items.interaction_count
        ) THEN 1
        ELSE 0
    END AS is_read,
    items.last_updated,
    items.source_uuid,
    items.fetch_progress,
    items.fetch_status,
    items.fetch_last_updated_at,
    items.fetch_retry_attempts,
    items.interaction_count,
    items.decrypted_size
FROM items
WHERE NOT EXISTS (
    SELECT 1
    FROM pending_events
    WHERE pending_events.item_uuid = items.uuid
        AND pending_events.type = 'item_deleted'
)
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events
        WHERE pending_events.source_uuid = items.source_uuid
            AND pending_events.type = 'source_deleted'
    )
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events
        WHERE pending_events.source_uuid = items.source_uuid
            AND pending_events.type = 'source_conversation_truncated'
            AND CAST(json_extract(pending_events.data, '$.upper_bound') AS INTEGER) >= items.interaction_count
    )
UNION ALL
SELECT
    json_extract(pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract(pending_events.data, '$.metadata') AS data,
    NULL AS version,
    json_extract(pending_events.data, '$.plaintext') AS plaintext,
    NULL AS filename,
    'reply' AS kind,
    1 AS is_read,
    NULL AS last_updated,
    json_extract(pending_events.data, '$.metadata.source') AS source_uuid,
    NULL AS fetch_progress,
    NULL AS fetch_status,
    NULL AS fetch_last_updated_at,
    NULL AS fetch_retry_attempts,
    json_extract(pending_events.data, '$.metadata.interaction_count') AS interaction_count,
    NULL AS decrypted_size
FROM pending_events
WHERE pending_events.type = 'reply_sent'
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events later
        WHERE (
            (
                later.source_uuid = json_extract(pending_events.data, '$.metadata.source')
                AND later.type = 'source_deleted'
            )
            OR
            (
                later.source_uuid = json_extract(pending_events.data, '$.metadata.source')
                AND later.type = 'source_conversation_truncated'
                AND CAST(json_extract(later.data, '$.upper_bound') AS INTEGER) >= CAST(json_extract(pending_events.data, '$.metadata.interaction_count') AS INTEGER)
            )
            OR
            (
                later.item_uuid = json_extract(pending_events.data, '$.metadata.uuid')
                AND later.type = 'item_deleted'
            )
        )
        AND later.snowflake_id > pending_events.snowflake_id
    );

-- migrate:down
DROP VIEW IF EXISTS items_projected;
CREATE VIEW items_projected AS
SELECT
    items.uuid,
    items.data,
    items.version,
    items.plaintext,
    items.filename,
    items.kind,
    CASE
        WHEN items.is_read THEN 1
        WHEN EXISTS (
            SELECT 1 FROM pending_events
            WHERE pending_events.item_uuid = items.uuid
                AND pending_events.type = 'item_seen'
        ) THEN 1
        WHEN EXISTS (
            SELECT 1 FROM pending_events
            WHERE pending_events.source_uuid = items.source_uuid
                AND pending_events.type = 'source_conversation_seen'
                AND CAST(json_extract(pending_events.data, '$.upper_bound') AS INTEGER) >= items.interaction_count
        ) THEN 1
        ELSE 0
    END AS is_read,
    items.last_updated,
    items.source_uuid,
    items.fetch_progress,
    items.fetch_status,
    items.fetch_last_updated_at,
    items.fetch_retry_attempts,
    items.interaction_count,
    items.decrypted_size
FROM items
WHERE NOT EXISTS (
    SELECT 1
    FROM pending_events
    WHERE pending_events.item_uuid = items.uuid
        AND pending_events.type = 'item_deleted'
)
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events
        WHERE pending_events.source_uuid = items.source_uuid
            AND pending_events.type = 'source_deleted'
    )
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events
        WHERE pending_events.source_uuid = items.source_uuid
            AND pending_events.type = 'source_conversation_truncated'
            AND CAST(json_extract(pending_events.data, '$.upper_bound') AS INTEGER) >= items.interaction_count
    )
UNION ALL
SELECT
    json_extract(pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract(pending_events.data, '$.metadata') AS data,
    NULL AS version,
    json_extract(pending_events.data, '$.plaintext') AS plaintext,
    NULL AS filename,
    'reply' AS kind,
    1 AS is_read,
    NULL AS last_updated,
    json_extract(pending_events.data, '$.metadata.source') AS source_uuid,
    NULL AS fetch_progress,
    NULL AS fetch_status,
    NULL AS fetch_last_updated_at,
    NULL AS fetch_retry_attempts,
    json_extract(pending_events.data, '$.metadata.interaction_count') AS interaction_count,
    NULL AS decrypted_size
FROM pending_events
WHERE pending_events.type = 'reply_sent'
    AND NOT EXISTS (
        SELECT 1
        FROM pending_events later
        WHERE (
            (
                later.source_uuid = json_extract(pending_events.data, '$.metadata.source')
                AND later.type = 'source_deleted'
            )
            OR
            (
                later.source_uuid = json_extract(pending_events.data, '$.metadata.source')
                AND later.type = 'source_conversation_truncated'
                AND CAST(json_extract(later.data, '$.upper_bound') AS INTEGER) >= CAST(json_extract(pending_events.data, '$.metadata.interaction_count') AS INTEGER)
            )
            OR
            (
                later.item_uuid = json_extract(pending_events.data, '$.metadata.uuid')
                AND later.type = 'item_deleted'
            )
        )
        AND later.snowflake_id > pending_events.snowflake_id
    );

ALTER TABLE pending_events DROP COLUMN local_cleanup_pending;
