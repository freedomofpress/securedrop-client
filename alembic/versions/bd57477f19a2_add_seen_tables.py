"""add seen tables

Revision ID: bd57477f19a2
Revises: a4bf1f58ce69
Create Date: 2020-10-20 22:43:46.743035

"""
import sqlalchemy as sa

from alembic import op

# revision identifiers, used by Alembic.
revision = 'bd57477f19a2'
down_revision = 'a4bf1f58ce69'
branch_labels = None
depends_on = None


def upgrade():
    """
    Create seen tables for files, messages, and replies.

    Once freedomofpress/securedrop#5503 is fixed, we can expect that journalist_id will never be
    NULL and then migrate these tables so that both of the foreign keys make up the primary key.
    We will also need to migrate any existing NULL journalist IDs in these tables (as well as the
    'replies' table) to a non-NULL id, most likely to the ID of a special global "deleted" User
    only to be used for historical data.
    """
    op.create_table('seen_files',
    sa.Column('id', sa.Integer(), nullable=False),
    sa.Column('file_id', sa.Integer(), nullable=False),
    sa.Column('journalist_id', sa.Integer(), nullable=True),
    sa.ForeignKeyConstraint(['file_id'], ['files.id'], name=op.f('fk_seen_files_file_id_files')),
    sa.ForeignKeyConstraint(['journalist_id'], ['users.id'], name=op.f('fk_seen_files_journalist_id_users')),
    sa.PrimaryKeyConstraint('id', name=op.f('pk_seen_files')),
    sa.UniqueConstraint('file_id', 'journalist_id', name=op.f('uq_seen_files_file_id'))
    )
    op.create_table('seen_messages',
    sa.Column('id', sa.Integer(), nullable=False),
    sa.Column('message_id', sa.Integer(), nullable=False),
    sa.Column('journalist_id', sa.Integer(), nullable=True),
    sa.ForeignKeyConstraint(['journalist_id'], ['users.id'], name=op.f('fk_seen_messages_journalist_id_users')),
    sa.ForeignKeyConstraint(['message_id'], ['messages.id'], name=op.f('fk_seen_messages_message_id_messages')),
    sa.PrimaryKeyConstraint('id', name=op.f('pk_seen_messages')),
    sa.UniqueConstraint('message_id', 'journalist_id', name=op.f('uq_seen_messages_message_id'))
    )
    op.create_table('seen_replies',
    sa.Column('id', sa.Integer(), nullable=False),
    sa.Column('reply_id', sa.Integer(), nullable=False),
    sa.Column('journalist_id', sa.Integer(), nullable=True),
    sa.ForeignKeyConstraint(['journalist_id'], ['users.id'], name=op.f('fk_seen_replies_journalist_id_users')),
    sa.ForeignKeyConstraint(['reply_id'], ['replies.id'], name=op.f('fk_seen_replies_reply_id_replies')),
    sa.PrimaryKeyConstraint('id', name=op.f('pk_seen_replies')),
    sa.UniqueConstraint('reply_id', 'journalist_id', name=op.f('uq_seen_replies_reply_id'))
    )


def downgrade():
    op.drop_table('seen_replies')
    op.drop_table('seen_messages')
    op.drop_table('seen_files')
