-- migrate:up
-- Retain safe filesystem cleanup identities after item and event rows disappear.
CREATE TABLE filesystem_cleanup_jobs (
    id TEXT PRIMARY KEY,
    target TEXT NOT NULL CHECK (target IN ('item', 'source')),
    source_uuid TEXT,
    item_uuid TEXT,
    metadata_item_uuid TEXT,
    status TEXT NOT NULL CHECK (status IN ('pending', 'quarantined')),
    reason TEXT,
    created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
    CHECK (
        (
            target = 'source'
            AND source_uuid IS NOT NULL
            AND item_uuid IS NULL
            AND metadata_item_uuid IS NULL
            AND status = 'pending'
        )
        OR
        (
            target = 'item'
            AND item_uuid IS NOT NULL
            AND (
                (status = 'pending' AND source_uuid IS NOT NULL)
                OR status = 'quarantined'
            )
        )
    )
);

CREATE INDEX idx_filesystem_cleanup_jobs_status
ON filesystem_cleanup_jobs(status, created_at, id);

-- migrate:down
DROP INDEX IF EXISTS idx_filesystem_cleanup_jobs_status;
DROP TABLE IF EXISTS filesystem_cleanup_jobs;
