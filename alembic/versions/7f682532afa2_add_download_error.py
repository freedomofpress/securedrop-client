"""add download error

Revision ID: 7f682532afa2
Revises: fb657f2ee8a7
Create Date: 2020-04-15 13:44:21.434312

"""
from alembic import op
import sqlalchemy as sa
from securedrop_client import db

# revision identifiers, used by Alembic.
revision = "7f682532afa2"
down_revision = "fb657f2ee8a7"
branch_labels = None
depends_on = None


CREATE_TABLE_FILES_NEW = """
    CREATE TABLE files (
        id INTEGER NOT NULL,
        uuid VARCHAR(36) NOT NULL,
        filename VARCHAR(255) NOT NULL,
        file_counter INTEGER NOT NULL,
        size INTEGER NOT NULL,
        download_url VARCHAR(255) NOT NULL,
        is_downloaded BOOLEAN DEFAULT 0 NOT NULL,
        is_decrypted BOOLEAN CONSTRAINT files_compare_is_downloaded_vs_is_decrypted CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        download_error_id INTEGER,
        is_read BOOLEAN DEFAULT 0 NOT NULL,
        source_id INTEGER NOT NULL,
        last_updated DATETIME NOT NULL,
        CONSTRAINT pk_files PRIMARY KEY (id),
        CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
        CONSTRAINT uq_files_uuid UNIQUE (uuid),
        CONSTRAINT ck_files_is_downloaded CHECK (is_downloaded IN (0, 1)),
        CONSTRAINT ck_files_is_decrypted CHECK (is_decrypted IN (0, 1)),
        CONSTRAINT fk_files_download_error_id_downloaderrors FOREIGN KEY(download_error_id) REFERENCES downloaderrors (id),
        CONSTRAINT ck_files_is_read CHECK (is_read IN (0, 1)),
        CONSTRAINT fk_files_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id)
);
"""

CREATE_TABLE_FILES_OLD = """
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
        CONSTRAINT files_compare_is_downloaded_vs_is_decrypted
           CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        CONSTRAINT ck_files_is_downloaded CHECK (is_downloaded IN (0, 1)),
        CONSTRAINT ck_files_is_read CHECK (is_read IN (0, 1)),
        CONSTRAINT ck_files_is_decrypted CHECK (is_decrypted IN (0, 1))
);
"""


CREATE_TABLE_MESSAGES_NEW = """
    CREATE TABLE messages (
        id INTEGER NOT NULL,
        uuid VARCHAR(36) NOT NULL,
        filename VARCHAR(255) NOT NULL,
        file_counter INTEGER NOT NULL,
        size INTEGER NOT NULL,
        download_url VARCHAR(255) NOT NULL,
        is_downloaded BOOLEAN DEFAULT 0 NOT NULL,
        is_decrypted BOOLEAN CONSTRAINT messages_compare_is_downloaded_vs_is_decrypted CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        download_error_id INTEGER,
        is_read BOOLEAN DEFAULT 0 NOT NULL,
        content TEXT CONSTRAINT ck_message_compare_download_vs_content CHECK (CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END),
        source_id INTEGER NOT NULL,
        last_updated DATETIME NOT NULL,
        CONSTRAINT pk_messages PRIMARY KEY (id),
        CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
        CONSTRAINT uq_messages_uuid UNIQUE (uuid),
        CONSTRAINT ck_messages_is_downloaded CHECK (is_downloaded IN (0, 1)),
        CONSTRAINT ck_messages_is_decrypted CHECK (is_decrypted IN (0, 1)),
        CONSTRAINT fk_messages_download_error_id_downloaderrors FOREIGN KEY(download_error_id) REFERENCES downloaderrors (id),
        CONSTRAINT ck_messages_is_read CHECK (is_read IN (0, 1)),
        CONSTRAINT fk_messages_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id)
    );
"""

CREATE_TABLE_MESSAGES_OLD = """
    CREATE TABLE messages (
        id INTEGER NOT NULL,
        uuid VARCHAR(36) NOT NULL,
        source_id INTEGER NOT NULL,
        filename VARCHAR(255) NOT NULL,
        file_counter INTEGER NOT NULL,
        size INTEGER NOT NULL,
        content TEXT,
        is_decrypted BOOLEAN,
        is_downloaded BOOLEAN DEFAULT 0 NOT NULL,
        is_read BOOLEAN DEFAULT 0 NOT NULL,
        download_url VARCHAR(255) NOT NULL,
        CONSTRAINT pk_messages PRIMARY KEY (id),
        CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
        CONSTRAINT uq_messages_uuid UNIQUE (uuid),
        CONSTRAINT fk_messages_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id),
        CONSTRAINT ck_message_compare_download_vs_content
           CHECK (CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END),
        CONSTRAINT messages_compare_is_downloaded_vs_is_decrypted
           CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        CONSTRAINT ck_messages_is_decrypted CHECK (is_decrypted IN (0, 1)),
        CONSTRAINT ck_messages_is_downloaded CHECK (is_downloaded IN (0, 1)),
        CONSTRAINT ck_messages_is_read CHECK (is_read IN (0, 1))
    );
"""


CREATE_TABLE_REPLIES_NEW = """
    CREATE TABLE replies (
        id INTEGER NOT NULL,
        uuid VARCHAR(36) NOT NULL,
        source_id INTEGER NOT NULL,
        filename VARCHAR(255) NOT NULL,
        file_counter INTEGER NOT NULL,
        size INTEGER,
        content TEXT,
        is_decrypted BOOLEAN,
        is_downloaded BOOLEAN,
        download_error_id INTEGER,
        journalist_id INTEGER,
        last_updated DATETIME NOT NULL,
        CONSTRAINT pk_replies PRIMARY KEY (id),
        CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
        CONSTRAINT uq_replies_uuid UNIQUE (uuid),
        CONSTRAINT fk_replies_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id),
        CONSTRAINT fk_replies_download_error_id_downloaderrors
            FOREIGN KEY(download_error_id) REFERENCES downloaderrors (id),
        CONSTRAINT fk_replies_journalist_id_users FOREIGN KEY(journalist_id) REFERENCES users (id),
        CONSTRAINT replies_compare_download_vs_content
            CHECK (CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END),
        CONSTRAINT replies_compare_is_downloaded_vs_is_decrypted
            CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        CONSTRAINT ck_replies_is_decrypted CHECK (is_decrypted IN (0, 1)),
        CONSTRAINT ck_replies_is_downloaded CHECK (is_downloaded IN (0, 1))
    );
"""

CREATE_TABLE_REPLIES_OLD = """
    CREATE TABLE replies (
        id INTEGER NOT NULL,
        uuid VARCHAR(36) NOT NULL,
        source_id INTEGER NOT NULL,
        filename VARCHAR(255) NOT NULL,
        file_counter INTEGER NOT NULL,
        size INTEGER,
        content TEXT,
        is_decrypted BOOLEAN,
        is_downloaded BOOLEAN,
        journalist_id INTEGER,
        CONSTRAINT pk_replies PRIMARY KEY (id),
        CONSTRAINT uq_messages_source_id_file_counter UNIQUE (source_id, file_counter),
        CONSTRAINT uq_replies_uuid UNIQUE (uuid),
        CONSTRAINT fk_replies_source_id_sources FOREIGN KEY(source_id) REFERENCES sources (id),
        CONSTRAINT fk_replies_journalist_id_users FOREIGN KEY(journalist_id) REFERENCES users (id),
        CONSTRAINT replies_compare_download_vs_content
            CHECK (CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END),
        CONSTRAINT replies_compare_is_downloaded_vs_is_decrypted
            CHECK (CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END),
        CONSTRAINT ck_replies_is_decrypted CHECK (is_decrypted IN (0, 1)),
        CONSTRAINT ck_replies_is_downloaded CHECK (is_downloaded IN (0, 1))
    );
"""


def upgrade():
    # ### commands auto generated by Alembic - please adjust! ###
    op.create_table(
        "downloaderrors",
        sa.Column("id", sa.Integer(), nullable=False),
        sa.Column("name", sa.String(length=36), nullable=False),
        sa.PrimaryKeyConstraint("id", name=op.f("pk_downloaderrors")),
        sa.UniqueConstraint("name", name=op.f("uq_downloaderrors_name")),
    )

    conn = op.get_bind()
    for name, member in db.DownloadErrorCodes.__members__.items():
        conn.execute("""INSERT INTO downloaderrors (name) VALUES (:name);""", name)

    op.rename_table("files", "files_tmp")
    op.rename_table("messages", "messages_tmp")
    op.rename_table("replies", "replies_tmp")

    conn.execute(CREATE_TABLE_FILES_NEW)
    conn.execute(CREATE_TABLE_MESSAGES_NEW)
    conn.execute(CREATE_TABLE_REPLIES_NEW)

    conn.execute("""
        INSERT INTO files
        (id, uuid, filename, file_counter, size, download_url,
               is_downloaded, is_read, is_decrypted, download_error_id, source_id)
        SELECT id, uuid, filename, file_counter, size, download_url,
               is_downloaded, is_read, is_decrypted, NULL, source_id
        FROM files_tmp
    """)
    conn.execute("""
        INSERT INTO messages
        (id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
         is_downloaded, is_read, download_error_id, download_url)
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
               is_downloaded, is_read, NULL, download_url
        FROM messages_tmp
    """)
    conn.execute("""
        INSERT INTO replies
        (id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
         is_downloaded, download_error_id, journalist_id)
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, NULL, journalist_id
        FROM replies_tmp
    """)

    # Delete the old tables.
    op.drop_table("files_tmp")
    op.drop_table("messages_tmp")
    op.drop_table("replies_tmp")

    # ### end Alembic commands ###


def downgrade():

    conn = op.get_bind()

    op.rename_table("files", "files_tmp")
    op.rename_table("messages", "messages_tmp")
    op.rename_table("replies", "replies_tmp")

    conn.execute(CREATE_TABLE_FILES_OLD)
    conn.execute(CREATE_TABLE_MESSAGES_OLD)
    conn.execute(CREATE_TABLE_REPLIES_OLD)

    conn.execute("""
        INSERT INTO files
        (id, uuid, filename, file_counter, size, download_url,
               is_downloaded, is_read, is_decrypted, source_id)
        SELECT id, uuid, filename, file_counter, size, download_url,
               is_downloaded, is_read, is_decrypted, source_id
        FROM files_tmp
    """)
    conn.execute("""
        INSERT INTO messages
        (id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
         is_downloaded, is_read, download_url)
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
               is_downloaded, is_read, download_url
        FROM messages_tmp
    """)
    conn.execute("""
        INSERT INTO replies
        (id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
         is_downloaded, journalist_id)
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, journalist_id
        FROM replies_tmp
    """)

    # Delete the old tables.
    op.drop_table("files_tmp")
    op.drop_table("messages_tmp")
    op.drop_table("replies_tmp")

    # Drop downloaderrors
    op.drop_table("downloaderrors")

    # ### end Alembic commands ###
