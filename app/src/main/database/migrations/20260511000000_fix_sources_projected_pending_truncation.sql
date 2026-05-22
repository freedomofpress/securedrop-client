-- migrate:up
-- Fix sources_projected to correctly project has_attachment and is_seen when
-- a source_conversation_truncated event is pending.
DROP VIEW IF EXISTS sources_projected;
CREATE VIEW
    sources_projected AS
WITH
    latest_starred AS (
        SELECT
            source_uuid,
            CASE
                WHEN type = 'source_starred' THEN true
                WHEN type = 'source_unstarred' THEN false
            END AS starred_value
        FROM
            (
                SELECT
                    source_uuid,
                    type,
                    ROW_NUMBER() OVER (
                        PARTITION BY
                            source_uuid
                        ORDER BY
                            snowflake_id DESC
                    ) AS rn
                FROM
                    pending_events
                WHERE
                    type IN ('source_starred', 'source_unstarred') AND
                    source_uuid IS NOT NULL
            ) latest
        WHERE
            rn = 1
    )
SELECT
    sources.uuid,
    CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set (sources.data, '$.is_starred', starred_value)
        ELSE sources.data
    END AS data,
    sources.version,
    -- Use server has_attachment by default; override only when there are pending events
    CASE
        WHEN EXISTS (
            SELECT
                1
            FROM
                pending_events pe
            WHERE
                pe.source_uuid = sources.uuid
        ) THEN CASE
            WHEN EXISTS (
                SELECT
                    1
                FROM
                    items_projected ip
                WHERE
                    ip.source_uuid = sources.uuid AND
                    ip.kind = 'file'
            ) THEN 1
            ELSE 0
        END
        ELSE sources.has_attachment
    END AS has_attachment,
    -- Use server is_seen by default; override only when there are pending events
    CASE
        WHEN EXISTS (
            SELECT
                1
            FROM
                pending_events pe
            WHERE
                pe.source_uuid = sources.uuid
        ) THEN CASE
            WHEN EXISTS (
                SELECT
                    1
                FROM
                    items_projected ip
                WHERE
                    ip.source_uuid = sources.uuid AND
                    ip.is_read = 0 AND
                    ip.kind != 'reply'
            ) THEN 0
            ELSE 1
        END
        ELSE sources.is_seen
    END AS is_seen
FROM
    sources
    LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
WHERE
    NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = sources.uuid AND
            pending_events.type = 'source_deleted'
    );
-- migrate:down
DROP VIEW IF EXISTS sources_projected;
CREATE VIEW
    sources_projected AS
WITH
    latest_starred AS (
        SELECT
            source_uuid,
            CASE
                WHEN type = 'source_starred' THEN true
                WHEN type = 'source_unstarred' THEN false
            END AS starred_value
        FROM
            (
                SELECT
                    source_uuid,
                    type,
                    ROW_NUMBER() OVER (
                        PARTITION BY
                            source_uuid
                        ORDER BY
                            snowflake_id DESC
                    ) AS rn
                FROM
                    pending_events
                WHERE
                    type IN ('source_starred', 'source_unstarred') AND
                    source_uuid IS NOT NULL
            ) latest
        WHERE
            rn = 1
    )
SELECT
    sources.uuid,
    CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set (sources.data, '$.is_starred', starred_value)
        ELSE sources.data
    END AS data,
    sources.version,
    sources.has_attachment,
    CASE
    -- if there are unread items for this source in items_projected, 
    -- then the source is unread
        WHEN EXISTS (
            SELECT
                1
            FROM
                items_projected ip
            WHERE
                ip.source_uuid = sources.uuid AND
                ip.is_read = 0
        ) THEN 0
        -- otherwise, the source is read
        ELSE 1
    END AS is_seen
FROM
    sources
    LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
WHERE
    NOT EXISTS (
        SELECT
            1
        FROM
            pending_events
        WHERE
            pending_events.source_uuid = sources.uuid AND
            pending_events.type = 'source_deleted'
    );