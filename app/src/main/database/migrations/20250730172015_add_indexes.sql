-- migrate:up
ALTER TABLE items ADD COLUMN source_uuid TEXT GENERATED ALWAYS AS (json_extract(data, '$.source')) VIRTUAL;
CREATE INDEX idx_items_source_uuid ON items(source_uuid);

ALTER TABLE items ADD COLUMN kind TEXT GENERATED ALWAYS AS (json_extract(data, '$.kind')) VIRTUAL;
CREATE INDEX idx_items_kind ON items(kind);

ALTER TABLE items ADD COLUMN is_read INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_read')) VIRTUAL;
CREATE INDEX idx_items_is_read ON items(is_read);

ALTER TABLE items ADD COLUMN last_updated INTEGER GENERATED ALWAYS AS (json_extract(data, '$.last_updated')) VIRTUAL;
CREATE INDEX idx_items_last_updated ON items(last_updated);

CREATE INDEX idx_sources_uuid ON sources(uuid);

-- migrate:down
ALTER TABLE items DROP COLUMN source_uuid;
DROP INDEX idx_items_source_uuid;

ALTER TABLE items DROP COLUMN kind;
DROP INDEX idx_items_kind;

ALTER TABLE items DROP COLUMN is_read;
DROP INDEX idx_items_is_read;

ALTER TABLE items DROP COLUMN last_updated;
DROP INDEX idx_items_last_updated;

DROP INDEX idx_sources_uuid;
