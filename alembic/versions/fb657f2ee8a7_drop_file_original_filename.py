"""drop File.original_filename

Revision ID: fb657f2ee8a7
Revises: 86b01b6290da
Create Date: 2020-01-23 18:55:09.857324

"""
import sqlalchemy as sa

from alembic import op

# revision identifiers, used by Alembic.
revision = "fb657f2ee8a7"
down_revision = "86b01b6290da"
branch_labels = None
depends_on = None


def upgrade():
    conn = op.get_bind()

    op.rename_table("files", "original_files")

    conn.execute(
        """
        CREATE TABLE files (
                id INTEGER NOT NULL,
                uuid VARCHAR(36) NOT NULL,
                filename VARCHAR(255) NOT NULL,
                file_counter INTEGER NOT NULL,
                size INTEGER NOT NULL,
                download_url VARCHAR(255) NOT NULL,
                is_downloaded BOOLEAN DEFAULT 0 NOT NULL,
                is_read BOOLEAN DEFAULT 0 NOT NULL,
                is_decrypted BOOLEAN,
                source_id INTEGER NOT NULL,
                CONSTRAINT pk_files PRIMARY KEY (id),
                CONSTRAINT fk_files_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id),
                CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
                CONSTRAINT uq_files_uuid UNIQUE (uuid),
                CONSTRAINT files_compare_is_downloaded_vs_is_decrypted CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
                CONSTRAINT ck_files_is_downloaded CHECK (is_downloaded IN (0, 1)),
                CONSTRAINT ck_files_is_read CHECK (is_read IN (0, 1)),
                CONSTRAINT ck_files_is_decrypted CHECK (is_decrypted IN (0, 1))
        )
        """
    )

    conn.execute(
        """
        INSERT INTO files
        (id, uuid, filename, file_counter, size, download_url, is_downloaded,
        is_decrypted, is_read, source_id)
        SELECT id, uuid, filename, file_counter, size, download_url, is_downloaded,
        is_decrypted, is_read, source_id
        FROM original_files
    """
    )

    op.drop_table("original_files")


def downgrade():
    op.add_column(
        "files",
        sa.Column(
            "original_filename",
            sa.VARCHAR(length=255),
            server_default=sa.text("''"),
            nullable=False,
        ),
    )
