# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022‒2023 The Freedom of the Press Foundation.
from typing import List

from sqlalchemy.orm.session import Session

from securedrop_client.db import File
from securedrop_client.storage import get_local_files


class Database:
    """Provide an interface to the database while abstracting session details."""

    def __init__(self, session: Session):
        super().__init__()
        self.session = session

    def get_files(self) -> List[File]:
        return get_local_files(self.session)
