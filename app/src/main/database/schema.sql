CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json
, is_read INTEGER DEFAULT 0, has_attachment INTEGER DEFAULT 0, show_message_preview INTEGER DEFAULT 0, message_preview TEXT);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
, source_uuid TEXT GENERATED ALWAYS AS (json_extract(data, '$.source')) VIRTUAL, kind TEXT GENERATED ALWAYS AS (json_extract(data, '$.kind')) VIRTUAL, is_read INTEGER GENERATED ALWAYS AS (json_extract(data, '$.is_read')) VIRTUAL, last_updated INTEGER GENERATED ALWAYS AS (json_extract(data, '$.last_updated')) VIRTUAL);
CREATE INDEX idx_items_source_uuid ON items(source_uuid);
CREATE INDEX idx_items_kind ON items(kind);
CREATE INDEX idx_items_is_read ON items(is_read);
CREATE INDEX idx_items_last_updated ON items(last_updated);
CREATE INDEX idx_sources_uuid ON sources(uuid);
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544'),
  ('20250730172015'),
  ('20250730180544');
