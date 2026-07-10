-- migrate:up
-- Keep an item's database identity aligned with its embedded metadata identity.

CREATE TRIGGER items_uuid_matches_metadata_insert
BEFORE INSERT ON items
FOR EACH ROW
WHEN NEW.data IS NOT NULL
    AND (
        SELECT count(*) != 1 OR min(value) IS NOT NEW.uuid
        FROM json_each(NEW.data)
        WHERE key = 'uuid'
    )
BEGIN
    SELECT RAISE(ABORT, 'items.uuid must match items.data.uuid');
END;

CREATE TRIGGER items_uuid_matches_metadata_update
BEFORE UPDATE OF uuid, data ON items
FOR EACH ROW
WHEN NEW.data IS NOT NULL
    AND (
        SELECT count(*) != 1 OR min(value) IS NOT NEW.uuid
        FROM json_each(NEW.data)
        WHERE key = 'uuid'
    )
BEGIN
    SELECT RAISE(ABORT, 'items.uuid must match items.data.uuid');
END;

-- Refuse to open a database that already contains a mismatched identity.
UPDATE items
SET data = data
WHERE data IS NOT NULL
    AND (
        SELECT count(*) != 1 OR min(value) IS NOT items.uuid
        FROM json_each(items.data)
        WHERE key = 'uuid'
    );

-- migrate:down

DROP TRIGGER IF EXISTS items_uuid_matches_metadata_update;
DROP TRIGGER IF EXISTS items_uuid_matches_metadata_insert;
