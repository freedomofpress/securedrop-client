CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json
, version text, is_seen integer generated always as (json_extract (data, '$.is_seen')) stored, has_attachment integer generated always as (json_extract (data, '$.has_attachment')) stored, show_message_preview integer default 0, message_preview text);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
, version text, kind text generated always as (json_extract (data, '$.kind')) stored, is_read integer generated always as (json_extract (data, '$.is_read')) stored, last_updated integer generated always as (json_extract (data, '$.last_updated')) stored, source_uuid text generated always as (json_extract (data, '$.source')), fetch_progress INTEGER, fetch_status INTEGER NOT NULL DEFAULT 0, fetch_last_updated_at timestamp, fetch_retry_attempts integer NOT NULL DEFAULT 0);
CREATE TABLE state_history (
    version text,
    updated timestamp default current_timestamp,
    id integer primary key autoincrement
);
CREATE VIEW state AS
SELECT *
FROM state_history
ORDER BY id DESC
LIMIT 1
/* state(version,updated,id) */;
CREATE INDEX idx_items_kind on items (kind);
CREATE INDEX idx_items_is_read on items (is_read);
CREATE INDEX idx_items_last_updated on items (last_updated);
CREATE INDEX idx_sources_uuid on sources (uuid);
CREATE INDEX idx_items_source_uuid on items (source_uuid);
CREATE TABLE journalists (
    uuid text primary key,
    data json,
    version text
);
CREATE INDEX idx_items_fetch_status ON items (fetch_status);
CREATE TABLE pending_events (
        snowflake_id INTEGER PRIMARY KEY,
        source_uuid INTEGER REFERENCES sources (uuid),
        -- pending items may not exist in the items table, so
        -- we don't add the fkey constraint
        item_uuid INTEGER,
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
CREATE VIEW sources_projected AS
WITH
    -- Select latest starred value from pending_events
    latest_starred AS (
        SELECT
            source_uuid,
            CASE
                WHEN type = 5 THEN true -- Starred
                WHEN type = 6 THEN false -- Unstarred
            END AS starred_value
        FROM
            (
                SELECT
                    source_uuid,
                    type
                FROM
                    pending_events
                WHERE
                    type in (5, 6) -- Starred or Unstarred
                ORDER BY
                    snowflake_id DESC
                LIMIT
                    1
            )
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
    )
/* sources_projected(uuid,data,version,has_attachment,show_message_preview,message_preview,is_seen) */;
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
    )
/* items_projected(uuid,data,version,plaintext,filename,kind,is_read,last_updated,source_uuid,fetch_progress,fetch_status,fetch_last_updated_at,fetch_retry_attempts) */;
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544'),
  ('20250722165416'),
  ('20250724191248'),
  ('20250725000000'),
  ('20250813000000'),
  ('20250819160236'),
  ('20250821184819'),
  ('20250930191810');
