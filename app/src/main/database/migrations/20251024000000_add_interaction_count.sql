-- migrate:up
ALTER TABLE items
ADD COLUMN interaction_count integer generated always as (json_extract (data, '$.interaction_count'));

CREATE INDEX idx_items_interaction_count on items (interaction_count);

-- Recreate items_projected view to include interaction_count
DROP VIEW items_projected;
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
            items.source_uuid = pending_events.source_uuid
            AND (
                -- type: SourceDeleted
                pending_events.type = 3
                -- type: SourceConversationDeleted
                OR pending_events.type = 4
            )
            -- No subsequent Unseen/Unstarred event
            AND NOT EXISTS (
                SELECT
                    1
                FROM
                    pending_events AS later
                WHERE
                    later.source_uuid = pending_events.source_uuid
                    AND (
                        -- type: Starred/Unstarred
                        later.type = 5
                        OR later.type = 6
                    )
                    AND later.snowflake_id > pending_events.snowflake_id
            )
    );

-- migrate:down
DROP VIEW items_projected;
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
            items.source_uuid = pending_events.source_uuid
            AND (
                -- type: SourceDeleted
                pending_events.type = 3
                -- type: SourceConversationDeleted
                OR pending_events.type = 4
            )
            -- No subsequent Unseen/Unstarred event
            AND NOT EXISTS (
                SELECT
                    1
                FROM
                    pending_events AS later
                WHERE
                    later.source_uuid = pending_events.source_uuid
                    AND (
                        -- type: Starred/Unstarred
                        later.type = 5
                        OR later.type = 6
                    )
                    AND later.snowflake_id > pending_events.snowflake_id
            )
    );

DROP INDEX IF EXISTS idx_items_interaction_count;
ALTER TABLE items DROP COLUMN interaction_count;
