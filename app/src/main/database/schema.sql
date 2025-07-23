CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json,
  version text,
  is_seen integer generated always as (json_extract (data, '$.is_seen')) stored,
  has_attachment integer generated always as (json_extract (data, '$.has_attachment')) stored,
  show_message_preview integer default 0,
  message_preview text
);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text,
  version text,
  source_uuid text generated always as (json_extract (data, '$.uuid')),
  kind text generated always as (json_extract (data, '$.kind')) stored,
  is_read integer generated always as (json_extract (data, '$.is_read')) stored,
  last_updated integer generated always as (json_extract (data, '$.last_updated')) stored
);
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
CREATE INDEX idx_items_source_uuid on items (source_uuid);
CREATE INDEX idx_items_kind on items (kind);
CREATE INDEX idx_items_is_read on items (is_read);
CREATE INDEX idx_items_last_updated on items (last_updated);
CREATE INDEX idx_sources_uuid on sources (uuid);
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544'),
  ('20250722165416'),
  ('20250724191248'),
  ('20250725000000');
