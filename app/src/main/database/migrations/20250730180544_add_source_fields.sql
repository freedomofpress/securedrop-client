-- migrate:up
ALTER TABLE sources ADD COLUMN is_read INTEGER DEFAULT 0;
ALTER TABLE sources ADD COLUMN has_attachment INTEGER DEFAULT 0;
ALTER TABLE sources ADD COLUMN show_message_preview INTEGER DEFAULT 0;
ALTER TABLE sources ADD COLUMN message_preview TEXT;

-- migrate:down
ALTER TABLE sources DROP COLUMN is_read;
ALTER TABLE sources DROP COLUMN has_attachment;
ALTER TABLE sources DROP COLUMN show_message_preview;
ALTER TABLE sources DROP COLUMN message_preview;

