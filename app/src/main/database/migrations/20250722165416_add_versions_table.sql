-- migrate:up
ALTER TABLE sources
ADD COLUMN version text;

ALTER TABLE items
ADD COLUMN version text;

CREATE TABLE state_history (
    version text,
    updated timestamp default current_timestamp,
    id integer primary key autoincrement
);

CREATE VIEW state AS 
SELECT * 
FROM state_history 
ORDER BY id DESC 
LIMIT 1; 

-- migrate:down
ALTER TABLE sources DROP COLUMN version;
ALTER TABLE items DROP COLUMN version;
DROP VIEW state;
DROP TABLE state_history;
