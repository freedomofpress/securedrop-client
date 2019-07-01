"""Add files.original_filename

Revision ID: bafdcae12f97
Revises: fecf1191b6f0
Create Date: 2019-06-24 13:45:47.239212

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = "bafdcae12f97"
down_revision = "fecf1191b6f0"
branch_labels = None
depends_on = None


def upgrade():
    op.add_column(
        "files",
        sa.Column("original_filename", sa.String(length=255), nullable=False, server_default=""),
    )

    conn = op.get_bind()
    conn.execute("""UPDATE files SET original_filename = replace(filename, '.gz.gpg', '');""")


def downgrade():
    with op.batch_alter_table('files', schema=None) as batch_op:
        batch_op.drop_column('original_filename')
