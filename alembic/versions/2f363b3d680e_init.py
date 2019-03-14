"""init

Revision ID: 2f363b3d680e
Revises:
Create Date: 2019-02-08 12:07:47.062397

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = '2f363b3d680e'
down_revision = None
branch_labels = None
depends_on = None


def upgrade():
    op.create_table(
        'sources',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('journalist_designation', sa.String(length=255), nullable=False),
        sa.Column('document_count', sa.Integer(), server_default='0', nullable=False),
        sa.Column('is_flagged', sa.Boolean(name='is_flagged'), server_default='0', nullable=True),
        sa.Column('public_key', sa.Text(), nullable=True),
        sa.Column('fingerprint', sa.String(length=64), nullable=True),
        sa.Column('interaction_count', sa.Integer(), server_default='0', nullable=False),
        sa.Column('is_starred', sa.Boolean(name='is_starred'), server_default='0', nullable=True),
        sa.Column('last_updated', sa.DateTime(), nullable=True),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_sources')),
        sa.UniqueConstraint('uuid', name=op.f('uq_sources_uuid'))
    )

    op.create_table(
        'users',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('username', sa.String(length=255), nullable=False),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_users')),
        sa.UniqueConstraint('uuid', name=op.f('uq_users_uuid'))
    )

    op.create_table(
        'files',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('download_url', sa.String(length=255), nullable=False),
        sa.Column('is_downloaded', sa.Boolean(name='is_downloaded'), server_default='0',
                  nullable=False),
        sa.Column('is_read', sa.Boolean(name='is_read'), server_default='0', nullable=False),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column('source_id', sa.Integer(), nullable=True),
        sa.ForeignKeyConstraint(['source_id'], ['sources.id'],
                                name=op.f('fk_files_source_id_sources')),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_files')),
        sa.UniqueConstraint('uuid', name=op.f('uq_files_uuid')),
        sa.CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                           name='files_compare_is_downloaded_vs_is_decrypted'),
    )

    op.create_table(
        'messages',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('download_url', sa.String(length=255), nullable=False),
        sa.Column('is_downloaded', sa.Boolean(name='is_downloaded'), server_default='0',
                  nullable=False),
        sa.Column('is_read', sa.Boolean(name='is_read'), server_default='0', nullable=False),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('source_id', sa.Integer(), nullable=True),
        sa.ForeignKeyConstraint(['source_id'], ['sources.id'],
                                name=op.f('fk_messages_source_id_sources')),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_messages')),
        sa.UniqueConstraint('uuid', name=op.f('uq_messages_uuid')),
        sa.CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                           name='messages_compare_download_vs_content'),
        sa.CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                           name='messages_compare_is_downloaded_vs_is_decrypted'),
        sa.CheckConstraint('CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
                           name='messages_compare_is_decrypted_vs_content'),
    )

    op.create_table(
        'replies',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=True),
        sa.Column('journalist_id', sa.Integer(), nullable=True),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('size', sa.Integer(), nullable=True),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('is_downloaded', sa.Boolean(name='is_downloaded'), nullable=True),
        sa.Column('is_decrypted', sa.Boolean(name='is_decrypted'), nullable=True),
        sa.ForeignKeyConstraint(['journalist_id'], ['users.id'],
                                name=op.f('fk_replies_journalist_id_users')),
        sa.ForeignKeyConstraint(['source_id'], ['sources.id'],
                                name=op.f('fk_replies_source_id_sources')),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_replies')),
        sa.UniqueConstraint('uuid', name=op.f('uq_replies_uuid')),
        sa.CheckConstraint('CASE WHEN is_downloaded = 0 THEN content IS NULL ELSE 1 END',
                           name='replies_compare_download_vs_content'),
        sa.CheckConstraint('CASE WHEN is_downloaded = 0 THEN is_decrypted IS NULL ELSE 1 END',
                           name='replies_compare_is_downloaded_vs_is_decrypted'),
        sa.CheckConstraint('CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END',
                           name='replies_compare_is_decrypted_vs_content'),
    )


def downgrade():
    op.drop_table('replies')
    op.drop_table('messages')
    op.drop_table('files')
    op.drop_table('users')
    op.drop_table('sources')
