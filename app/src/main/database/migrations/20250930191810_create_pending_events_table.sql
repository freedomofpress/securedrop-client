-- migrate:up
CREATE TABLE
    pending_events (
        snowflake_id TEXT PRIMARY KEY,
        source_uuid TEXT REFERENCES sources (uuid),
        -- pending items may not exist in the items table, so 
        -- we don't add the fkey constraint
        item_uuid TEXT,
        type TEXT NOT NULL,
        -- additional event data
        data json,
        -- only one of source_uuid OR item_uuid is set
        CHECK (
            NOT (
                source_uuid IS NOT NULL
                AND item_uuid IS NOT NULL
            )
        )
    );

CREATE VIEW
    sources_projected AS
WITH
    -- Select latest starred value from pending_events
    latest_starred AS (
        SELECT
            source_uuid,
            CASE
                WHEN type = 'source_starred' THEN true
                WHEN type = 'source_unstarred' THEN false
            END as starred_value
        FROM
            (
                SELECT
                    source_uuid,
                    type,
                    -- Order events to select most recent
                    ROW_NUMBER() OVER (
                        PARTITION BY
                            source_uuid
                        ORDER BY
                            snowflake_id DESC
                    ) AS rn
                FROM
                    pending_events
                WHERE
                    type IN ('source_starred', 'source_unstarred')
                    AND source_uuid IS NOT NULL
            ) latest
        WHERE
            rn = 1
    )
SELECT
    sources.uuid,
    -- project Starred/Unstarred event 
    CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set (sources.data, '$.is_starred', starred_value)
        ELSE sources.data
    END AS data,
    sources.version,
    sources.has_attachment,
    sources.show_message_preview,
    sources.message_preview,
    -- project Seen event
    CASE
        WHEN EXISTS (
            SELECT
                1
            FROM
                pending_events
            WHERE
                pending_events.source_uuid = sources.uuid
                AND pending_events.type = 'item_seen'
        ) THEN 1
        ELSE sources.is_seen
    END AS is_seen
FROM
    sources
    LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
WHERE
    -- project SourceDeleted event 
    NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = sources.uuid
            AND pending_events.type = 'source_deleted'
    );

CREATE VIEW
    items_projected AS
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
    items.fetch_retry_attempts
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
    json_extract (pending_events.data, '$.uuid') AS uuid,
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
    NULL as fetch_retry_attempts
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
                (
                    later.source_uuid = json_extract (pending_events.data, '$.metadata.source')
                    AND later.type IN ('source_deleted', 'source_conversation_deleted')
                )
                OR (
                    later.item_uuid = json_extract (pending_events.data, '$.metadata.uuid')
                    AND later.type = 'item_deleted'
                )
            )
            AND later.snowflake_id > pending_events.snowflake_id
    );

-- migrate:down
DROP VIEW IF EXISTS items_projected;

DROP VIEW IF EXISTS sources_projected;

DROP TABLE IF EXISTS pending_events;