-- migrate:up
-- Type-checking: Don't allow `items.data.kind` to change after it's been set.

CREATE TRIGGER items_kind_immutable
BEFORE UPDATE OF data ON items
FOR EACH ROW
WHEN json_extract(OLD.data, '$.kind') IS NOT NULL
    AND json_extract(NEW.data, '$.kind') IS NOT json_extract(OLD.data, '$.kind')
BEGIN
    SELECT RAISE(ABORT, 'items.kind is immutable');
END;

-- migrate:down

DROP TRIGGER IF EXISTS items_kind_immutable;
