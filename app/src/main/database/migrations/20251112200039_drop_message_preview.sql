-- migrate:up
-- Recreate sources_projected view
DROP VIEW sources_projected;

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

ALTER TABLE sources
DROP COLUMN message_preview;

ALTER TABLE sources
DROP COLUMN show_message_preview;

-- Add sorted items view 
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
ALTER TABLE sources
ADD COLUMN message_preview TEXT;

ALTER TABLE sources
ADD COLUMN show_message_preview INTEGER DEFAULT 0;

DROP VIEW sources_projected;

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

DROP VIEW sorted_items;