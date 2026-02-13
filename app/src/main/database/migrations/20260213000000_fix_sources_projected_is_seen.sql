-- migrate:up

-- sorted_items depends on items_projected, so drop it first
DROP VIEW IF EXISTS sorted_items;

-- sources_projected will reference items_projected, drop it before recreating items_projected
DROP VIEW IF EXISTS sources_projected;
DROP VIEW IF EXISTS items_projected;

-- Recreate items_projected with is_read projected from pending item_seen events
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
            AND pending_events.type IN ('source_deleted', 'source_conversation_deleted')
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
                AND later.type IN ('source_deleted', 'source_conversation_deleted')
            )
            OR
            (
                later.item_uuid = json_extract(pending_events.data, '$.metadata.uuid')
                AND later.type = 'item_deleted'
            )
        )
        AND later.snowflake_id > pending_events.snowflake_id
    );

-- Recreate sources_projected with correct is_seen logic:
-- is_seen is true if sources.is_seen is truthy (server says seen),
-- otherwise fall back to checking all items_projected have is_read = true
CREATE VIEW sources_projected AS
WITH latest_starred AS (
    SELECT
        source_uuid,
        CASE
            WHEN type = 'source_starred' THEN true
            WHEN type = 'source_unstarred' THEN false
        END AS starred_value
    FROM (
        SELECT
            source_uuid,
            type,
            ROW_NUMBER() OVER (
                PARTITION BY source_uuid
                ORDER BY snowflake_id DESC
            ) AS rn
        FROM pending_events
        WHERE type IN ('source_starred', 'source_unstarred')
            AND source_uuid IS NOT NULL
    ) latest
    WHERE rn = 1
)
SELECT
    sources.uuid,
    CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set(sources.data, '$.is_starred', starred_value)
        ELSE sources.data
    END AS data,
    sources.version,
    sources.has_attachment,
    CASE
        WHEN sources.is_seen THEN 1
        WHEN EXISTS (
            SELECT 1 FROM items_projected ip
            WHERE ip.source_uuid = sources.uuid AND ip.is_read = 0
        ) THEN 0
        WHEN NOT EXISTS (
            SELECT 1 FROM items_projected ip
            WHERE ip.source_uuid = sources.uuid
        ) THEN 0
        ELSE 1
    END AS is_seen
FROM sources
LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
WHERE NOT EXISTS (
    SELECT 1
    FROM pending_events
    WHERE pending_events.source_uuid = sources.uuid
        AND pending_events.type = 'source_deleted'
);

-- Recreate sorted_items
CREATE VIEW sorted_items AS
SELECT
    *,
    ROW_NUMBER() OVER (
        PARTITION BY source_uuid
        ORDER BY interaction_count DESC
    ) AS rn
FROM items_projected;

-- migrate:down

DROP VIEW IF EXISTS sorted_items;
DROP VIEW IF EXISTS sources_projected;
DROP VIEW IF EXISTS items_projected;

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
            AND pending_events.type IN ('source_deleted', 'source_conversation_deleted')
    )
UNION ALL
SELECT
    json_extract(pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract(pending_events.data, '$.metadata') AS data,
    NULL AS version,
    json_extract(pending_events.data, '$.plaintext') AS plaintext,
    NULL AS filename,
    'reply' AS kind,
    NULL AS is_read,
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
                AND later.type IN ('source_deleted', 'source_conversation_deleted')
            )
            OR
            (
                later.item_uuid = json_extract(pending_events.data, '$.metadata.uuid')
                AND later.type = 'item_deleted'
            )
        )
        AND later.snowflake_id > pending_events.snowflake_id
    );

CREATE VIEW sources_projected AS
WITH latest_starred AS (
    SELECT
        source_uuid,
        CASE
            WHEN type = 'source_starred' THEN true
            WHEN type = 'source_unstarred' THEN false
        END AS starred_value
    FROM (
        SELECT
            source_uuid,
            type,
            ROW_NUMBER() OVER (
                PARTITION BY source_uuid
                ORDER BY snowflake_id DESC
            ) AS rn
        FROM pending_events
        WHERE type IN ('source_starred', 'source_unstarred')
            AND source_uuid IS NOT NULL
    ) latest
    WHERE rn = 1
)
SELECT
    sources.uuid,
    CASE
        WHEN latest_starred.starred_value IS NOT NULL THEN json_set(sources.data, '$.is_starred', starred_value)
        ELSE sources.data
    END AS data,
    sources.version,
    sources.has_attachment,
    CASE
        WHEN EXISTS (
            SELECT 1
            FROM pending_events
            WHERE pending_events.source_uuid = sources.uuid
                AND pending_events.type = 'item_seen'
        ) THEN 1
        ELSE sources.is_seen
    END AS is_seen
FROM sources
LEFT JOIN latest_starred ON latest_starred.source_uuid = sources.uuid
WHERE NOT EXISTS (
    SELECT 1
    FROM pending_events
    WHERE pending_events.source_uuid = sources.uuid
        AND pending_events.type = 'source_deleted'
);

CREATE VIEW sorted_items AS
SELECT
    *,
    ROW_NUMBER() OVER (
        PARTITION BY source_uuid
        ORDER BY interaction_count DESC
    ) AS rn
FROM items_projected;
