CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json
, version text);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
, version text, source_uuid text generated always as (json_extract (data, '$.uuid')));
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
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544'),
  ('20250722165416'),
  ('20250724191248');
