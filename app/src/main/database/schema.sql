CREATE TABLE IF NOT EXISTS "schema_migrations" (version varchar(128) primary key);
CREATE TABLE sources (
  uuid text primary key,
  data json
);
CREATE TABLE items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
);
-- Dbmate schema migrations
INSERT INTO "schema_migrations" (version) VALUES
  ('20250710180544');
