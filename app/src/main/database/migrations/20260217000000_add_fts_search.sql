-- migrate:up
CREATE VIRTUAL TABLE search_index USING fts5 (
    source_uuid UNINDEXED,
    item_uuid UNINDEXED,
    type UNINDEXED,
    content,
    tokenize = 'unicode61'
);

-- migrate:down
DROP TABLE IF EXISTS search_index;