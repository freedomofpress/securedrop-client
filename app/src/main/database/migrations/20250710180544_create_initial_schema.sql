-- migrate:up
create table
  sources (
    uuid text primary key,
    data json,
    is_seen integer generated always as (json_extract (data, '$.is_seen')) stored,
    has_attachment integer generated always as (json_extract (data, '$.has_attachment')) stored,
    show_message_preview integer default 0,
    message_preview text
  );

create table
  items (
    uuid text primary key,
    data json,
    plaintext text,
    filename text,
    source_uuid text generated always as (json_extract (data, '$.source')) stored,
    kind text generated always as (json_extract (data, '$.kind')) stored,
    is_read integer generated always as (json_extract (data, '$.is_read')) stored,
    last_updated integer generated always as (json_extract (data, '$.last_updated')) stored
  );

create index idx_items_source_uuid on items (source_uuid);

create index idx_items_kind on items (kind);

create index idx_items_is_read on items (is_read);

create index idx_items_last_updated on items (last_updated);

create index idx_sources_uuid on sources (uuid);

-- migrate:down
drop table if exists items;

drop table if exists sources;
