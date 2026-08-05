-- migrate:up
-- Source key material is trust-on-first-use: once a source row has key
-- metadata, the server must not be able to replace it through later syncs.

CREATE TRIGGER sources_key_material_immutable
BEFORE UPDATE OF data ON sources
FOR EACH ROW
WHEN (
    json_extract(OLD.data, '$.public_key') IS NOT NULL
    AND json_extract(NEW.data, '$.public_key') IS NOT json_extract(OLD.data, '$.public_key')
) OR (
    json_extract(OLD.data, '$.fingerprint') IS NOT NULL
    AND json_extract(NEW.data, '$.fingerprint') IS NOT json_extract(OLD.data, '$.fingerprint')
)
BEGIN
    SELECT RAISE(ABORT, 'sources key material is immutable');
END;

-- migrate:down

DROP TRIGGER IF EXISTS sources_key_material_immutable;
