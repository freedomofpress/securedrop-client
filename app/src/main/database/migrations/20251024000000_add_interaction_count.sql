-- migrate:up
ALTER TABLE items
ADD COLUMN interaction_count integer generated always as (json_extract (data, '$.interaction_count'));

-- Recreate items_projected view to include interaction_count
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
    NULL as fetch_retry_attempts,
    json_extract (pending_events.data, '$.metadata.interaction_count') AS interaction_count
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

ALTER TABLE items DROP COLUMN interaction_count;
