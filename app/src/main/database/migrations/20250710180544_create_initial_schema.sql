-- migrate:up
create table sources (
  uuid text primary key,
  data json
);

create table items (
  uuid text primary key,
  data json,
  plaintext text,
  filename text
);

-- migrate:down
drop table if exists items;
drop table if exists sources;
