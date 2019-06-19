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
    op.drop_constraint('messages_compare_is_decrypted_vs_content', 'messages')
    op.drop_constraint('replies_compare_is_decrypted_vs_content', 'replies')


def downgrade():
    op.create_check_constraint(
        'messages_compare_is_decrypted_vs_content',
        'messages',
        'CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END')
    op.create_check_constraint(
        'replies_compare_is_decrypted_vs_content',
        'replies',
        'CASE WHEN is_decrypted = 0 THEN content IS NULL ELSE 1 END')
