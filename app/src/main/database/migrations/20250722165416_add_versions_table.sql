-- migrate:up
ALTER TABLE sources
ADD COLUMN version text;

ALTER TABLE items
ADD COLUMN version text;

CREATE TABLE version (
    version text
);

-- migrate:down
ALTER TABLE sources DROP COLUMN version;
ALTER TABLE items DROP COLUMN version;
DROP TABLE version;
