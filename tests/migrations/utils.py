# -*- coding: utf-8 -*-
import random
import string
from datetime import datetime
from typing import Optional
from uuid import uuid4

from sqlalchemy import text
from sqlalchemy.orm.session import Session

from securedrop_client.db import DownloadError, ReplySendStatus, Source

random.seed("ᕕ( ᐛ )ᕗ")


def random_bool() -> bool:
    return bool(random.getrandbits(1))


def bool_or_none() -> Optional[bool]:
    return random.choice([None, True, False])


def random_name() -> str:
    len = random.randint(1, 100)
    return random_chars(len)


def random_username() -> str:
    len = random.randint(3, 64)
    return random_chars(len)


def random_chars(len: int, chars: str = string.printable) -> str:
    return "".join([random.choice(chars) for _ in range(len)])


def random_ascii_chars(len: int, chars: str = string.ascii_lowercase):
    return "".join([random.choice(chars) for _ in range(len)])


def random_datetime(nullable: bool = False):
    if nullable and random_bool():
        return None
    else:
        return datetime(
            year=random.randint(1, 9999),
            month=random.randint(1, 12),
            day=random.randint(1, 28),
            hour=random.randint(0, 23),
            minute=random.randint(0, 59),
            second=random.randint(0, 59),
            microsecond=random.randint(0, 1000),
        )


def add_source(session: Session) -> None:
    params = {
        "uuid": str(uuid4()),
        "journalist_designation": random_chars(50),
        "last_updated": random_datetime(nullable=True),
        "interaction_count": random.randint(0, 1000),
    }
    sql = """
    INSERT INTO sources (
        uuid,
        journalist_designation,
        last_updated,
        interaction_count
    )
    VALUES (
        :uuid,
        :journalist_designation,
        :last_updated,
        :interaction_count
    )
    """
    session.execute(text(sql), params)


def add_user(session: Session, uuid: Optional[str] = None) -> None:
    if not uuid:
        journalist_uuid = str(uuid4())
    else:
        journalist_uuid = uuid

    params = {
        "uuid": journalist_uuid,
        "username": random_username(),
    }
    sql = """
    INSERT INTO users (uuid, username)
    VALUES (:uuid, :username)
    """
    session.execute(text(sql), params)


def add_reply(session: Session, journalist_id: int, source_id: int) -> None:
    is_downloaded = random_bool() if random_bool() else None
    is_decrypted = random_bool() if is_downloaded else None

    download_errors = session.query(DownloadError).all()
    download_error_ids = [error.id for error in download_errors]

    content = random_chars(1000) if is_downloaded else None

    source = session.query(Source).filter_by(id=source_id).one()

    file_counter = len(source.collection) + 1

    params = {
        "uuid": str(uuid4()),
        "journalist_id": journalist_id,
        "source_id": source_id,
        "filename": random_chars(50) + "-reply.gpg",
        "file_counter": file_counter,
        "size": random.randint(0, 1024 * 1024 * 500),
        "content": content,
        "is_downloaded": is_downloaded,
        "is_decrypted": is_decrypted,
        "download_error_id": random.choice(download_error_ids),
        "last_updated": random_datetime(),
    }
    sql = """
    INSERT INTO replies
    (
        uuid,
        journalist_id,
        source_id,
        filename,
        file_counter,
        size,
        content,
        is_downloaded,
        is_decrypted,
        download_error_id,
        last_updated
    )
    VALUES
    (
        :uuid,
        :journalist_id,
        :source_id,
        :filename,
        :file_counter,
        :size,
        :content,
        :is_downloaded,
        :is_decrypted,
        :download_error_id,
        :last_updated
    )
    """
    session.execute(text(sql), params)


def add_draft_reply(session: Session, journalist_id: int, source_id: int) -> None:
    reply_send_statuses = session.query(ReplySendStatus).all()
    reply_send_status_ids = [reply_send_status.id for reply_send_status in reply_send_statuses]

    content = random_chars(1000)

    source = session.query(Source).filter_by(id=source_id).one()

    file_counter = len(source.collection) + 1

    params = {
        "uuid": str(uuid4()),
        "journalist_id": journalist_id,
        "source_id": source_id,
        "file_counter": file_counter,
        "content": content,
        "send_status_id": random.choice(reply_send_status_ids),
        "timestamp": random_datetime(),
    }

    sql = """
    INSERT INTO draftreplies
    (
        uuid,
        journalist_id,
        source_id,
        file_counter,
        content,
        send_status_id,
        timestamp
    )
    VALUES
    (
        :uuid,
        :journalist_id,
        :source_id,
        :file_counter,
        :content,
        :send_status_id,
        :timestamp
    )
    """
    session.execute(text(sql), params)
