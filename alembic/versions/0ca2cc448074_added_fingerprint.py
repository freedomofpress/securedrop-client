"""added fingerprint

Revision ID: 0ca2cc448074
Revises: cd0fbb73bf8e
Create Date: 2018-11-30 18:55:23.007169

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = '0ca2cc448074'
down_revision = 'cd0fbb73bf8e'
branch_labels = None
depends_on = None


def upgrade():
    op.add_column('sources', sa.Column('fingerprint', sa.String(length=64), nullable=True))


def downgrade():
    op.drop_column('sources', 'fingerprint')
