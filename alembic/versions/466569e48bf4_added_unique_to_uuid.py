"""added unique to uuid

Revision ID: 466569e48bf4
Revises: 0ca2cc448074
Create Date: 2018-12-03 09:40:48.931574

"""
from alembic import op


# revision identifiers, used by Alembic.
revision = '466569e48bf4'
down_revision = '0ca2cc448074'
branch_labels = None
depends_on = None


def upgrade():
    op.create_unique_constraint(op.f('uq_users_uuid'), 'users', ['uuid'])


def downgrade():
    op.drop_constraint(op.f('uq_users_uuid'), 'users', type_='unique')
