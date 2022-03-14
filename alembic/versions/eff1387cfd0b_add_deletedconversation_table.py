"""add deletedconversation table

Revision ID: eff1387cfd0b
Revises: bd57477f19a2
Create Date: 2022-02-24 13:11:22.227528

"""
import sqlalchemy as sa

from alembic import op

# revision identifiers, used by Alembic.
revision = "eff1387cfd0b"
down_revision = "bd57477f19a2"
branch_labels = None
depends_on = None


def upgrade():
    # Add deletedconversation table to manage locally-deleted records
    # and ensure they do not get re-downloaded to the database during
    # a network race condition.
    # UUID was chosen as PK to avoid storing data such as source_id that
    # could divulge information about the source account creation timeline.
    # Note that records in this table are purged every 15 seconds.
    op.create_table(
        "deletedconversation",
        sa.Column("uuid", sa.String(length=36), nullable=False),
        sa.PrimaryKeyConstraint("uuid", name=op.f("pk_deletedconversation")),
    )


def downgrade():
    op.drop_table("deletedconversation")
