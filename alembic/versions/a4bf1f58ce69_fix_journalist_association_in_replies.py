"""fix journalist association in replies table

Revision ID: a4bf1f58ce69
Revises: 7f682532afa2
Create Date: 2020-10-20 13:49:53.035383

"""
from alembic import op

# revision identifiers, used by Alembic.
revision = "a4bf1f58ce69"
down_revision = "7f682532afa2"
branch_labels = None
depends_on = None


def upgrade():
    """
    Fix reply association with journalist by updating journalist uuid to journalist id in the
    journalist_id column for the replies and draftreplies tables.
    """
    conn = op.get_bind()
    cursor = conn.execute(
        """
        SELECT journalist_id
        FROM replies, users
        WHERE journalist_id=users.uuid;
    """
    )

    replies_with_incorrect_associations = cursor.fetchall()
    if replies_with_incorrect_associations:
        conn.execute(
            """
            UPDATE replies
            SET journalist_id=
            (
                SELECT users.id
                FROM users
                WHERE journalist_id=users.uuid
            )
            WHERE exists
            (
                SELECT users.id
                FROM users
                WHERE journalist_id=users.uuid
            );
        """
        )

    cursor = conn.execute(
        """
        SELECT journalist_id
        FROM draftreplies, users
        WHERE journalist_id=users.uuid;
    """
    )

    draftreplies_with_incorrect_associations = cursor.fetchall()
    if draftreplies_with_incorrect_associations:
        conn.execute(
            """
            UPDATE draftreplies
            SET journalist_id=
            (
                SELECT users.id
                FROM users
                WHERE journalist_id=users.uuid
            )
            WHERE exists
            (
                SELECT users.id
                FROM users
                WHERE journalist_id=users.uuid
            );
        """
        )


def downgrade():
    """
    We do not want to undo this bug fix, because nothing will break if we downgrade to an earlier
    version of the client.
    """
    pass
