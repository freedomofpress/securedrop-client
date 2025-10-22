-- migrate:up
CREATE TABLE
    pending_events (
        snowflake_id TEXT PRIMARY KEY,
        source_uuid TEXT REFERENCES sources (uuid),
        -- pending items may not exist in the items table, so 
        -- we don't add the fkey constraint
        item_uuid TEXT,
        type INTEGER NOT NULL,
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
                WHEN type = 5 THEN true -- Starred
                WHEN type = 6 THEN false -- Unstarred
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
                    type IN (5, 6) -- Starred or Unstarred
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
                -- type: Seen
                AND pending_events.type = 7
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
            -- type: SourceDeleted
            AND pending_events.type = 3
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
            -- type: ItemDeleted 
            AND pending_events.type = 2
    )
    -- project SourceDeleted, SourceConversationDeleted event
    AND NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = items.source_uuid
            -- type: SourceDeleted, SourceConversationDeleted
            AND pending_events.type IN (3, 4)
    )
    -- project ReplySent event 
UNION ALL
SELECT
    json_extract (pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract (pending_events.data, '$.metadata') as data,
    NULL as version,
    json_extract (pending_events.data, '$.text') AS plaintext,
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
    -- type: ReplySent
    pending_events.type = 1
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
                    AND later.type IN (3, 4)
                )
                OR
                -- ItemDeleted
                (
                    later.item_uuid = json_extract (pending_events.data, '$.metadata.uuid')
                    AND later.type = 2
                )
            )
            AND later.snowflake_id > pending_events.snowflake_id
    );

-- migrate:down
DROP VIEW IF EXISTS items_projected;

DROP VIEW IF EXISTS sources_projected;

DROP TABLE IF EXISTS pending_events;