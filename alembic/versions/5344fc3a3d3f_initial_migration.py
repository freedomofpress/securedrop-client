"""Initial migration

Revision ID: 5344fc3a3d3f
Revises:
Create Date: 2018-07-18 18:11:06.781732

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = '5344fc3a3d3f'
down_revision = None
branch_labels = None
depends_on = None


def upgrade():
    op.create_table(
        'users',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('username', sa.String(length=255), nullable=False),
        sa.PrimaryKeyConstraint('id'),
        sa.UniqueConstraint('username')
    )
    op.create_table(
        'sources',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('journalist_designation', sa.String(length=255),
                  nullable=False),
        sa.Column('is_flagged', sa.Boolean(name='ck_sources_is_flagged'),
                  nullable=True,
                  server_default="false"),
        sa.Column('public_key', sa.Text(), nullable=True),
        sa.Column('interaction_count', sa.Integer(), nullable=False,
                  server_default="0"),
        sa.Column('is_starred', sa.Boolean(name='ck_sources_is_starred'),
                  nullable=True,
                  server_default="false"),
        sa.Column('last_updated', sa.DateTime(), nullable=True),
        sa.PrimaryKeyConstraint('id'),
        sa.UniqueConstraint('uuid')
    )
    op.create_table(
        'replies',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=True),
        sa.Column('journalist_id', sa.Integer(), nullable=True),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('is_downloaded', sa.Boolean(
            name='ck_replies_is_downloaded'), nullable=True),
        sa.ForeignKeyConstraint(['journalist_id'], ['users.id'], ),
        sa.ForeignKeyConstraint(['source_id'], ['sources.id'], ),
        sa.PrimaryKeyConstraint('id'),
        sa.UniqueConstraint('uuid')
    )
    op.create_table(
        'submissions',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('filename', sa.String(length=255), nullable=False),
        sa.Column('size', sa.Integer(), nullable=False),
        sa.Column('is_downloaded',
                  sa.Boolean(name='ck_submissions_is_downloaded'),
                  nullable=True),
        sa.Column('is_read',
                  sa.Boolean(name='ck_submissions_is_read'),
                  nullable=True),
        sa.Column('source_id', sa.Integer(), nullable=True),
        sa.Column('download_url', sa.String(length=255), nullable=False),
        sa.ForeignKeyConstraint(['source_id'], ['sources.id'], ),
        sa.PrimaryKeyConstraint('id'),
        sa.UniqueConstraint('uuid')
    )


def downgrade():
    op.drop_table('users')
    op.drop_table('submissions')
    op.drop_table('replies')
    op.drop_table('sources')
