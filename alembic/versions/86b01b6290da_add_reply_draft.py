"""add reply draft

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

    # Set the initial in-progress send statuses: PENDING, FAILED
    conn = op.get_bind()
    conn.execute('''
        INSERT INTO replysendstatuses
        ('name')
        VALUES
        ('PENDING'), 
        ('FAILED');
    ''')

    op.create_table(
        'draftreplies',
        sa.Column('id', sa.Integer(), nullable=False),
        sa.Column('uuid', sa.String(length=36), nullable=False),
        sa.Column('timestamp', sa.DateTime(), nullable=False),
        sa.Column('source_id', sa.Integer(), nullable=False),
        sa.Column('journalist_id', sa.Integer(), nullable=True),
        sa.Column('file_counter', sa.Integer(), nullable=False),
        sa.Column('content', sa.Text(), nullable=True),
        sa.Column('send_status_id', sa.Integer(), nullable=True),
        sa.PrimaryKeyConstraint('id', name=op.f('pk_draftreplies')),
        sa.UniqueConstraint('uuid', name=op.f('uq_draftreplies_uuid')),
        sa.ForeignKeyConstraint(
            ['source_id'],
            ['sources.id'],
            name=op.f('fk_draftreplies_source_id_sources')),
        sa.ForeignKeyConstraint(
            ['journalist_id'],
            ['users.id'],
            name=op.f('fk_draftreplies_journalist_id_users')),
        sa.ForeignKeyConstraint(
            ['send_status_id'],
            ['replysendstatuses.id'],
            op.f('fk_draftreplies_send_status_id_replysendstatuses'),
        )
    )


def downgrade():
    op.drop_table('draftreplies')
    op.drop_table('replysendstatuses')
