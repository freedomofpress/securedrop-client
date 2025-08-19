-- migrate:up
CREATE TABLE IF NOT EXISTS journalists (
    uuid text primary key,
    data json,
    version text
);

-- migrate:down
DROP TABLE journalists;
