"""merge DraftReply into Reply

Revision ID: dcba730b8834
Revises: b646a89cee64
Create Date: 2023-05-03 15:47:22.424886

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = "dcba730b8834"
down_revision = "b646a89cee64"
branch_labels = None
depends_on = None


def upgrade():
    op.execute(
        """INSERT INTO replies (
            id,
            uuid,
            source_id,
            journalist_id,
            file_counter,
            content,
            state
            )
        SELECT
            id,
            uuid,
            source_id,
            journalist_id,
            file_counter,
            content,
            CASE send_status_id
                WHEN 1 THEN 'Ready'
                WHEN 2 THEN 'SendFailed'
            END
        FROM draftreplies"""
    )

    op.drop_table("replysendstatuses")
    op.drop_table("draftreplies")


def downgrade():
    op.execute(
        """INSERT INTO draftreplies (
            id,
            uuid,
            source_id,
            journalist_id,
            file_counter,
            content,
            send_status_id
            )
        SELECT
            id,
            uuid,
            source_id,
            journalist_id,
            file_counter,
            content,
            CASE state
                WHEN 'Ready' THEN 1
                WHEN 'SendFailed' THEN 2
            END
        FROM replies"""
    )

    op.create_table(
        "draftreplies",
        sa.Column("id", sa.INTEGER(), nullable=False),
        sa.Column("uuid", sa.VARCHAR(length=36), nullable=False),
        sa.Column("timestamp", sa.DATETIME(), nullable=False),
        sa.Column("source_id", sa.INTEGER(), nullable=False),
        sa.Column("journalist_id", sa.INTEGER(), nullable=True),
        sa.Column("file_counter", sa.INTEGER(), nullable=False),
        sa.Column("content", sa.TEXT(), nullable=True),
        sa.Column("send_status_id", sa.INTEGER(), nullable=True),
        sa.Column("sending_pid", sa.INTEGER(), nullable=True),
        sa.ForeignKeyConstraint(
            ["journalist_id"], ["users.id"], name="fk_draftreplies_journalist_id_users"
        ),
        sa.ForeignKeyConstraint(
            ["send_status_id"],
            ["replysendstatuses.id"],
            name="fk_draftreplies_send_status_id_replysendstatuses",
        ),
        sa.ForeignKeyConstraint(
            ["source_id"], ["sources.id"], name="fk_draftreplies_source_id_sources"
        ),
        sa.PrimaryKeyConstraint("id", name="pk_draftreplies"),
        sa.UniqueConstraint("uuid", name="uq_draftreplies_uuid"),
    )
    op.create_table(
        "replysendstatuses",
        sa.Column("id", sa.INTEGER(), nullable=False),
        sa.Column("name", sa.VARCHAR(length=36), nullable=False),
        sa.PrimaryKeyConstraint("id", name="pk_replysendstatuses"),
        sa.UniqueConstraint("name", name="uq_replysendstatuses_name"),
    )
