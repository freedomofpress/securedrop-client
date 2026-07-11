-- migrate:up

CREATE TABLE pagination_state (
    id INTEGER PRIMARY KEY CHECK (id = 1),
    generation INTEGER NOT NULL
);

INSERT INTO pagination_state (id, generation) VALUES (1, 0);

CREATE TRIGGER items_pagination_generation_insert
AFTER INSERT ON items
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

CREATE TRIGGER items_pagination_generation_update
AFTER UPDATE OF uuid, data ON items
WHEN OLD.uuid IS NOT NEW.uuid
    OR json_extract(OLD.data, '$.source') IS NOT
        json_extract(NEW.data, '$.source')
    OR json_extract(OLD.data, '$.interaction_count') IS NOT
        json_extract(NEW.data, '$.interaction_count')
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

CREATE TRIGGER items_pagination_generation_delete
AFTER DELETE ON items
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

CREATE TRIGGER pending_events_pagination_generation_insert
AFTER INSERT ON pending_events
WHEN NEW.type IN (
    'item_deleted',
    'reply_sent',
    'source_conversation_truncated',
    'source_deleted'
)
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

CREATE TRIGGER pending_events_pagination_generation_update
AFTER UPDATE OF snowflake_id, type, data, source_uuid, item_uuid ON pending_events
WHEN (
        OLD.type IS NOT NEW.type
        AND (
            OLD.type IN (
                'item_deleted',
                'reply_sent',
                'source_conversation_truncated',
                'source_deleted'
            )
            OR NEW.type IN (
                'item_deleted',
                'reply_sent',
                'source_conversation_truncated',
                'source_deleted'
            )
        )
    )
    OR (
        OLD.type = 'item_deleted'
        AND NEW.type = 'item_deleted'
        AND (
            OLD.snowflake_id IS NOT NEW.snowflake_id
            OR OLD.item_uuid IS NOT NEW.item_uuid
        )
    )
    OR (
        OLD.type = 'reply_sent'
        AND NEW.type = 'reply_sent'
        AND (
            OLD.snowflake_id IS NOT NEW.snowflake_id
            OR json_extract(OLD.data, '$.metadata.uuid') IS NOT
                json_extract(NEW.data, '$.metadata.uuid')
            OR json_extract(OLD.data, '$.metadata.source') IS NOT
                json_extract(NEW.data, '$.metadata.source')
            OR json_extract(OLD.data, '$.metadata.interaction_count') IS NOT
                json_extract(NEW.data, '$.metadata.interaction_count')
        )
    )
    OR (
        OLD.type = 'source_conversation_truncated'
        AND NEW.type = 'source_conversation_truncated'
        AND (
            OLD.snowflake_id IS NOT NEW.snowflake_id
            OR OLD.source_uuid IS NOT NEW.source_uuid
            OR json_extract(OLD.data, '$.upper_bound') IS NOT
                json_extract(NEW.data, '$.upper_bound')
        )
    )
    OR (
        OLD.type = 'source_deleted'
        AND NEW.type = 'source_deleted'
        AND (
            OLD.snowflake_id IS NOT NEW.snowflake_id
            OR OLD.source_uuid IS NOT NEW.source_uuid
        )
    )
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

CREATE TRIGGER pending_events_pagination_generation_delete
AFTER DELETE ON pending_events
WHEN OLD.type IN (
    'item_deleted',
    'reply_sent',
    'source_conversation_truncated',
    'source_deleted'
)
BEGIN
    UPDATE pagination_state SET generation = generation + 1 WHERE id = 1;
END;

-- migrate:down

DROP TRIGGER IF EXISTS pending_events_pagination_generation_delete;
DROP TRIGGER IF EXISTS pending_events_pagination_generation_update;
DROP TRIGGER IF EXISTS pending_events_pagination_generation_insert;
DROP TRIGGER IF EXISTS items_pagination_generation_delete;
DROP TRIGGER IF EXISTS items_pagination_generation_update;
DROP TRIGGER IF EXISTS items_pagination_generation_insert;
DROP TABLE IF EXISTS pagination_state;
