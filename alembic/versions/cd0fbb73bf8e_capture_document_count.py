"""Capture document count

Revision ID: cd0fbb73bf8e
Revises: 5344fc3a3d3f
Create Date: 2018-11-10 18:10:23.847838

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = 'cd0fbb73bf8e'
down_revision = '5344fc3a3d3f'
branch_labels = None
depends_on = None


def upgrade():
    op.add_column('sources', sa.Column(
        'document_count', sa.Integer(), nullable=False, server_default='0'))


def downgrade():
    op.drop_column('sources', 'document_count')
