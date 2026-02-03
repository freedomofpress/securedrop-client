-- migrate:up

-- Sources table
CREATE TABLE sources (
    uuid TEXT PRIMARY KEY,
    data JSON,
    version TEXT,
    is_seen INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_seen')) STORED,
    has_attachment INTEGER GENERATED ALWAYS AS (json_extract(data, '$.has_attachment')) STORED
);

-- Items table
CREATE TABLE items (
    uuid TEXT PRIMARY KEY,
    data JSON,
    plaintext TEXT,
    filename TEXT,
    version TEXT,
    source_uuid TEXT GENERATED ALWAYS AS (json_extract(data, '$.source')) STORED,
    kind TEXT GENERATED ALWAYS AS (json_extract(data, '$.kind')) STORED,
    is_read INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_read')) STORED,
    last_updated INTEGER GENERATED ALWAYS AS (json_extract(data, '$.last_updated')) STORED,
    fetch_progress INTEGER,
    fetch_status INTEGER NOT NULL DEFAULT 0,
    fetch_last_updated_at TIMESTAMP,
    fetch_retry_attempts INTEGER NOT NULL DEFAULT 0,
    interaction_count INTEGER GENERATED ALWAYS AS (json_extract(data, '$.interaction_count')),
    decrypted_size INTEGER
);

-- Journalists table
CREATE TABLE journalists (
    uuid TEXT PRIMARY KEY,
    data JSON,
    version TEXT
);

-- State history table
CREATE TABLE state_history (
    version TEXT,
    updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    id INTEGER PRIMARY KEY AUTOINCREMENT
);

-- Pending events table
CREATE TABLE pending_events (
    snowflake_id TEXT PRIMARY KEY,
    source_uuid TEXT REFERENCES sources(uuid) ON DELETE CASCADE,
    item_uuid TEXT REFERENCES items(uuid) ON DELETE CASCADE,
    type TEXT NOT NULL,
    data JSON,
    CHECK (NOT (source_uuid IS NOT NULL AND item_uuid IS NOT NULL))
);

-- State view
CREATE VIEW state AS
SELECT *
FROM state_history
ORDER BY id DESC
LIMIT 1;

-- Sources projected view
/*
This view projects pending events onto sources:
- Select latest starred value from pending_events
- Order events to select most recent
- project Starred/Unstarred event
- project Seen event
- project SourceDeleted event
*/
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

-- Items projected view
/*
This view projects pending events onto items:
- project ItemDeleted event
- project SourceDeleted, SourceConversationDeleted event
- project ReplySent event
- Check that there is no later overriding deletion
  - SourceDeleted or SourceConversationDeleted
  - ItemDeleted
*/
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

-- Sorted items view
CREATE VIEW sorted_items AS
SELECT
    *,
    ROW_NUMBER() OVER (
        PARTITION BY source_uuid
        ORDER BY interaction_count DESC
    ) AS rn
FROM items_projected;

-- Performance indexes
CREATE INDEX idx_items_kind ON items(kind);
CREATE INDEX idx_items_is_read ON items(is_read);
CREATE INDEX idx_items_last_updated ON items(last_updated);
CREATE INDEX idx_sources_uuid ON sources(uuid);
CREATE INDEX idx_items_source_uuid ON items(source_uuid);
CREATE INDEX idx_items_fetch_status ON items(fetch_status);

-- migrate:down
DROP VIEW IF EXISTS sorted_items;
DROP VIEW IF EXISTS items_projected;
DROP VIEW IF EXISTS sources_projected;
DROP VIEW IF EXISTS state;
DROP TABLE IF EXISTS pending_events;
DROP TABLE IF EXISTS state_history;
DROP TABLE IF EXISTS journalists;
DROP TABLE IF EXISTS items;
DROP TABLE IF EXISTS sources;
