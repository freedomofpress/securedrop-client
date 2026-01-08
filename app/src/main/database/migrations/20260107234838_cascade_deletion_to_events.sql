-- migrate:up
DROP TABLE pending_events;
CREATE TABLE pending_events (
        snowflake_id TEXT PRIMARY KEY,
        -- See `schema.md` for details on how these foreign-key relationships
        -- work over the lifecycles of sources and items versus their pending
        -- events.
        source_uuid TEXT REFERENCES sources (uuid) ON DELETE CASCADE,
        item_uuid TEXT REFERENCES items (uuid) on DELETE CASCADE,
        type TEXT NOT NULL,
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

-- migrate:down
DROP TABLE pending_events;
CREATE TABLE pending_events (
        snowflake_id TEXT PRIMARY KEY,
        source_uuid TEXT REFERENCES sources (uuid),
        -- pending items may not exist in the items table, so
        -- we don't add the fkey constraint
        item_uuid TEXT,
        type TEXT NOT NULL,
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