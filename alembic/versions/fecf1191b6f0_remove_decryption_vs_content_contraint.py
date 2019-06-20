"""remove decryption_vs_content contraint

Revision ID: fecf1191b6f0
Revises: 2f363b3d680e
Create Date: 2019-06-18 19:14:17.862910

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = 'fecf1191b6f0'
down_revision = '2f363b3d680e'
branch_labels = None
depends_on = None


def upgrade():
    # Save existing tables we want to modify.
    op.rename_table('messages', 'messages_tmp')
    op.rename_table('replies', 'replies_tmp')

    # Create new tables without the constraint.
    op.create_table(
        'messages',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('file_counter', sa.Integer(), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column(
            'is_downloaded',
            sa.Boolean(name='is_downloaded'),
            server_default=sa.text("0"),
            nullable=False),
        sa.Column(
            'is_read',
            sa.Boolean(name='is_read'),
            server_default=sa.text("0"),
            nullable=False),
        sa.Column('download_url', sa.String(length=255), nullable=False),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_messages')),
        sa.UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
        sa.UniqueConstraint('uuid', name=op.f('uq_messages_uuid')),
        sa.ForeignKeyConstraint(
            ['source_id'],
            ['sources.id'],
            name=op.f('fk_messages_source_id_sources')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
            name=op.f('ck_message_compare_download_vs_content')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
            name='messages_compare_is_downloaded_vs_is_decrypted'))

    op.create_table(
        'replies',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('file_counter', sa.Integer(), nullable=False),
        sa.Column('size', sa.Integer(), nullable=True),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column('is_downloaded', sa.Boolean(name='is_downloaded'), nullable=True),
        sa.Column('journalist_id', sa.Integer(), nullable=True),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_replies')),
        sa.UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
        sa.UniqueConstraint('uuid', name=op.f('uq_replies_uuid')),
        sa.ForeignKeyConstraint(
            ['source_id'],
            ['sources.id'],
            name=op.f('fk_replies_source_id_sources')),
        sa.ForeignKeyConstraint(
            ['journalist_id'],
            ['users.id'],
            name=op.f('fk_replies_journalist_id_users')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
            name='replies_compare_download_vs_content'),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
            name='replies_compare_is_downloaded_vs_is_decrypted'))

    # Copy existing data into new tables.
    conn = op.get_bind()
    conn.execute('''
        INSERT INTO messages
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
               is_downloaded, is_read, download_url
        FROM messages_tmp
    ''')
    conn.execute('''
        INSERT INTO replies
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, journalist_id
        FROM replies_tmp
    ''')

    # Delete the old tables.
    op.drop_table('messages_tmp')
    op.drop_table('replies_tmp')


def downgrade():
    # Save existing tables we want to modify.
    op.rename_table('messages', 'messages_tmp')
    op.rename_table('replies', 'replies_tmp')

    # Create new tables with the constraint.
    op.create_table(
        'messages',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('file_counter', sa.Integer(), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column(
            'is_downloaded',
            sa.Boolean(name='is_downloaded'),
            server_default=sa.text("0"),
            nullable=False),
        sa.Column(
            'is_read',
            sa.Boolean(name='is_read'),
            server_default=sa.text("0"),
            nullable=False),
        sa.Column('download_url', sa.String(length=255), nullable=False),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_messages')),
        sa.UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
        sa.UniqueConstraint('uuid', name=op.f('uq_messages_uuid')),
        sa.ForeignKeyConstraint(
            ['source_id'],
            ['sources.id'],
            name=op.f('fk_messages_source_id_sources')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
            name=op.f('ck_message_compare_download_vs_content')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
            name='messages_compare_is_downloaded_vs_is_decrypted'),
        sa.CheckConstraint(
            'CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
            name='messages_compare_is_decrypted_vs_content'))

    op.create_table(
        'replies',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('file_counter', sa.Integer(), nullable=False),
        sa.Column('size', sa.Integer(), nullable=True),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column('is_downloaded', sa.Boolean(name='is_downloaded'), nullable=True),
        sa.Column('journalist_id', sa.Integer(), nullable=True),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_replies')),
        sa.UniqueConstraint('source_id', 'file_counter', name='uq_messages_source_id_file_counter'),
        sa.UniqueConstraint('uuid', name=op.f('uq_replies_uuid')),
        sa.ForeignKeyConstraint(
            ['source_id'],
            ['sources.id'],
            name=op.f('fk_replies_source_id_sources')),
        sa.ForeignKeyConstraint(
            ['journalist_id'],
            ['users.id'],
            name=op.f('fk_replies_journalist_id_users')),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
            name='replies_compare_download_vs_content'),
        sa.CheckConstraint(
            'CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
            name='replies_compare_is_downloaded_vs_is_decrypted'),
        sa.CheckConstraint(
            'CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
            name='replies_compare_is_decrypted_vs_content'))

    # Copy existing data into new tables.
    conn = op.get_bind()
    conn.execute('''
        INSERT INTO messages
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
               is_downloaded, download_url, is_read
        FROM messages_tmp
    ''')
    conn.execute('''
        INSERT INTO replies
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, journalist_id
        FROM replies_tmp
    ''')

    # Delete the old tables.
    op.drop_table('messages_tmp')
    op.drop_table('replies_tmp')
