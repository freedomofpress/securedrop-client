CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
    uuid text primary key,
    data json,
    is_read integer default 0,
    has_attachment integer default 0,
    show_message_preview integer default 0,
    message_preview text
  );
CREATE TABLE items (
    uuid text primary key,
    data json,
    plaintext text,
    filename text,
    source_uuid text generated always as (json_extract (data, '$.source')) stored,
    kind text generated always as (json_extract (data, '$.kind')) stored,
    is_read integer generated always as (json_extract (data, '$.is_read')) stored,
    last_updated integer generated always as (json_extract (data, '$.last_updated')) stored
  );
CREATE INDEX idx_items_source_uuid on items (source_uuid);
CREATE INDEX idx_items_kind on items (kind);
CREATE INDEX idx_items_is_read on items (is_read);
CREATE INDEX idx_items_last_updated on items (last_updated);
CREATE INDEX idx_sources_uuid on sources (uuid);
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544');
