CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json
, version text, is_seen integer generated always as (json_extract (data, '$.is_seen')) stored, has_attachment integer generated always as (json_extract (data, '$.has_attachment')) stored, show_message_preview integer default 0, message_preview text);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
, version text, kind text generated always as (json_extract (data, '$.kind')) stored, is_read integer generated always as (json_extract (data, '$.is_read')) stored, last_updated integer generated always as (json_extract (data, '$.last_updated')) stored, source_uuid text generated always as (json_extract (data, '$.source')), fetch_progress INTEGER, fetch_status INTEGER NOT NULL DEFAULT 0, fetch_last_updated_at timestamp, fetch_retry_attempts integer NOT NULL DEFAULT 0);
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
CREATE INDEX idx_items_kind on items (kind);
CREATE INDEX idx_items_is_read on items (is_read);
CREATE INDEX idx_items_last_updated on items (last_updated);
CREATE INDEX idx_sources_uuid on sources (uuid);
CREATE INDEX idx_items_source_uuid on items (source_uuid);
CREATE TABLE journalists (
    uuid text primary key,
    data json,
    version text
);
CREATE INDEX idx_items_fetch_status ON items (fetch_status);
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544'),
  ('20250722165416'),
  ('20250724191248'),
  ('20250725000000'),
  ('20250813000000'),
  ('20250819160236'),
  ('20250821184819');
