-- migrate:up
-- Remove search index entries whose source row no longer exists
DELETE FROM search_index
WHERE
  source_uuid NOT IN (
    SELECT
      uuid
    FROM
      sources
  );

-- Remove search index entries whose item row no longer exists
DELETE FROM search_index
WHERE
  item_uuid IS NOT NULL
  AND item_uuid NOT IN (
    SELECT
      uuid
    FROM
      items
  );

-- migrate:down
-- no-op: deleted index entries cannot be recovered