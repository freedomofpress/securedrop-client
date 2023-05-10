"""Reply: require unique filename, not file_counter

Revision ID: a3d544c9e528
Revises: dcba730b8834
Create Date: 2023-05-10 16:34:44.402098

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = "a3d544c9e528"
down_revision = "dcba730b8834"
branch_labels = None
depends_on = None


def upgrade():
    with op.batch_alter_table("replies") as batch_op:
        # NB: Original constraint name does not match table name (cd09ee8).
        batch_op.drop_constraint("uq_messages_source_id_file_counter", type_="unique")
        batch_op.create_unique_constraint(
            "uq_replies_source_id_filename", ["source_id", "filename"]
        )


def downgrade():
    with op.batch_alter_table("replies") as batch_op:
        batch_op.drop_constraint("uq_replies_source_id_filename", type_="unique")
        # NB: Restored constraint name does not match table name (cd09ee8).
        batch_op.create_unique_constraint(
            "uq_messages_source_id_file_counter", ["source_id", "file_counter"]
        )
