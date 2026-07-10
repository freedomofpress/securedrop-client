-- migrate:up
-- Source identity: Don't allow `items.data.source` to change after it's been set.

CREATE TRIGGER items_source_immutable
BEFORE UPDATE OF data ON items
FOR EACH ROW
WHEN json_extract(OLD.data, '$.source') IS NOT NULL
    AND json_extract(NEW.data, '$.source') IS NOT json_extract(OLD.data, '$.source')
BEGIN
    SELECT RAISE(ABORT, 'items.source is immutable');
END;

-- migrate:down

DROP TRIGGER IF EXISTS items_source_immutable;
