"""add Reply state machine

Revision ID: b646a89cee64
Revises: 414627c04463
Create Date: 2023-05-02 17:01:11.781862

"""
from alembic import op
import sqlalchemy as sa


# revision identifiers, used by Alembic.
revision = "b646a89cee64"
down_revision = "414627c04463"
branch_labels = None
depends_on = None


def upgrade():
    """
    Add Reply.state, then derive its values from the legacy state columns in
    batch mode before dropping them.

    We have to do the non-addition operations in batch mode because SQLite
    doesn't support column-level ALTER or DROP statements.[1]

    [1]: https://alembic.sqlalchemy.org/en/latest/ops.html#alembic.operations.Operations.batch_alter_table
    """
    op.add_column(
        "replies", sa.Column("state", sa.String(length=100), nullable=False, server_default="Ready")
    )
    op.execute("UPDATE replies SET state = 'Ready' WHERE is_decrypted IS 1")
    op.execute("UPDATE replies SET state = 'DecryptionFailed' WHERE is_decrypted IS 0")
    op.execute("UPDATE replies SET state = 'DownloadFailed' WHERE is_downloaded IS 0")

    with op.batch_alter_table("replies") as batch_op:

        batch_op.drop_column("is_downloaded")
        batch_op.drop_column("is_decrypted")


def downgrade():
    """
    Restore the legacy state columns, then derive their values from Reply.state
    before dropping it.

    See above re: batch mode.
    """
    op.add_column("replies", sa.Column("is_decrypted", sa.BOOLEAN(), nullable=True))
    op.add_column("replies", sa.Column("is_downloaded", sa.BOOLEAN(), nullable=True))
    op.execute("UPDATE replies SET is_downloaded = 1 AND is_decrypted = 1 WHERE state = 'Ready'")
    op.execute(
        "UPDATE replies SET is_downloaded = 1 AND is_decrypted = 0 WHERE state = 'DecryptionFailed'"
    )
    op.execute(
        "UPDATE replies SET is_downloaded = 0 AND is_decrypted = 0 WHERE state = 'DonloadFailed'"
    )

    with op.batch_alter_table("replies") as batch_op:
        batch_op.drop_column("state")
