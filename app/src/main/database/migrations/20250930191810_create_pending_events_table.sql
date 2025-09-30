-- migrate:up
CREATE TABLE pending_events (
    snowflake_id INTEGER PRIMARY KEY,

    -- only one of source_uuid OR item_uuid is set
    source_uuid INTEGER REFERENCES sources(uuid),
    item_uuid INTEGER REFERENCES items(uuid),

    type INTEGER NOT NULL,

    -- additional event data
    data json
);

ALTER TABLE sources
ADD COLUMN is_starred text generated always as (json_extract (data, '$.is_starred'));

CREATE VIEW sources_projected AS 
SELECT 
    sources.uuid,
    -- project Starred/Unstarred event 
    CASE
        WHEN EXISTS (
            SELECT 1 
            FROM pending_events 
            WHERE pending_events.source_uuid = sources.uuid 
            -- type: Starred
            AND pending_events.type = 5
        ) THEN json_set(sources.data, '$.is_starred', true)
        WHEN EXISTS (
            SELECT 1
            FROM pending_events 
            WHERE pending_events.source_uuid = sources.uuid 
            -- type: Unstarred
            AND pending_events.type = 6
        ) THEN json_set(sources.data, '$.is_starred', false)
        ELSE sources.data
    END AS data,
    sources.version,
    sources.has_attachment,
    sources.show_message_preview,
    sources.message_preview,
    -- project Seen event
    CASE 
        WHEN EXISTS (
            SELECT 1 
            FROM pending_events
            WHERE pending_events.source_uuid = sources.uuid 
            -- type: Seen
            AND pending_events.type = 7
        )
        THEN 1 
        ELSE sources.is_seen
    END AS is_seen
FROM sources
-- project SourceDeleted event 
WHERE NOT EXISTS (
    SELECT 1 
    FROM pending_events 
    WHERE pending_events.source_uuid = sources.uuid 
    -- type: SourceDeleted
    AND pending_events.type = 3
);

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
FROM items 
-- project ReplyDeleted event
WHERE NOT EXISTS (
    SELECT 1 
    FROM pending_events 
    WHERE pending_events.item_uuid = items.uuid 
    -- type: ReplyDeleted 
    AND pending_events.type = 2
)
-- project SourceDeleted, SourceConversationDeleted event
AND NOT EXISTS (
    SELECT 1 
    FROM pending_events 
    WHERE pending_events.source_uuid = items.source_uuid 
    -- type: SourceDeleted, SourceConversationDeleted
    AND pending_events.type IN (3, 4) 
)
-- project ReplySent event 
UNION ALL 
SELECT 
    json_extract(pending_events.data, '$.metadata.uuid') AS uuid,
    json_extract(pending_events.data, '$.metadata') as data,
    NULL as version,
    json_extract(pending_events.data, '$.text') AS plaintext,
    NULL as filename,
    'reply' AS kind,
    NULL as is_read,
    NULL as last_updated,
    json_extract(pending_events.data, '$.metadata.source') AS source_uuid,
    NULL as fetch_progress,
    NULL as fetch_status,
    NULL as fetch_last_updated_at,
    NULL as fetch_retry_attempts
FROM pending_events 
-- type: ReplySent
WHERE pending_events.type = 1;

-- migrate:down
DROP VIEW IF EXISTS items_projected;
DROP VIEW IF EXISTS sources_projected;
ALTER TABLE sources DROP COLUMN is_starred;
DROP TABLE IF EXISTS pending_events;
