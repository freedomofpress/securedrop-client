"""add first_name, last_name, fullname, initials

Revision ID: 36a79ffcfbfb
Revises: fecf1191b6f0
Create Date: 2019-06-28 15:21:50.893256

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = '36a79ffcfbfb'
down_revision = 'bafdcae12f97'
branch_labels = None
depends_on = None


def upgrade():
    op.add_column('users', sa.Column('firstname', sa.String(length=64), nullable=True))
    op.add_column('users', sa.Column('lastname', sa.String(length=64), nullable=True))


def downgrade():
    with op.batch_alter_table('users', schema=None) as batch_op:
        batch_op.drop_column('lastname')
        batch_op.drop_column('firstname')
