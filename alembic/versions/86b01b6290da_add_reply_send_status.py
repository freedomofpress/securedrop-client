"""add reply send status

Revision ID: 86b01b6290da
Revises: 36a79ffcfbfb
Create Date: 2019-10-17 09:45:07.643076

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = '86b01b6290da'
down_revision = '36a79ffcfbfb'
branch_labels = None
depends_on = None


def upgrade():
    op.create_table('replysendstatuses',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('name', sa.String(length=36), nullable=False),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_replysendstatuses')),
        sa.UniqueConstraint('name', name=op.f('uq_replysendstatuses_name'))
    )

    # Set the initial statuses: PENDING, FAILED, SUCCEEDED
    conn = op.get_bind()
    conn.execute('''
        INSERT INTO replysendstatuses
        ('name')
        VALUES
        ('PENDING'), 
        ('SUCCEEDED'),
        ('FAILED');
    ''')

    op.rename_table('replies', 'replies_tmp')
    op.add_column('replies_tmp', sa.Column('send_status_id', sa.Integer(), nullable=True))
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
        sa.Column('send_status_id', sa.Integer(), nullable=True),
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
        sa.ForeignKeyConstraint(
            ['send_status_id'],
            ['replysendstatuses.id'],
            op.f('fk_replies_send_status_replysendstatuses'),
        )
    )

    conn.execute('''
        INSERT INTO replies
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, journalist_id, send_status_id
        FROM replies_tmp
    ''')
    op.drop_table('replies_tmp')


def downgrade():
    op.rename_table('replies', 'replies_tmp')

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

    conn = op.get_bind()
    conn.execute('''
        INSERT INTO replies
        SELECT id, uuid, source_id, filename, file_counter, size, content, is_decrypted,
              is_downloaded, journalist_id
        FROM replies_tmp
    ''')
    op.drop_table('replies_tmp')
    op.drop_table('replysendstatuses')
