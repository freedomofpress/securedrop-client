import os
import subprocess

import pytest
from sqlalchemy import text
from sqlalchemy.exc import OperationalError
from sqlalchemy.orm import scoped_session

ENUMS = {
    "downloaderrors": ["CHECKSUM_ERROR", "DECRYPTION_ERROR"],
    "replysendstatuses": ["PENDING", "FAILED"],
}


class UpgradeTester:
    """Enum tables exist and contains the expected values."""

    def __init__(self, homedir: str, session: scoped_session) -> None:
        subprocess.check_call(["sqlite3", os.path.join(homedir, "svs.sqlite"), ".databases"])
        self.session = session

    def load_data(self):
        pass

    def check_upgrade(self):
        for table, values in ENUMS.items():
            for value in values:
                result = self.session.execute(
                    text(f"SELECT * FROM {table} WHERE name = '{value}'")  # noqa: S608
                ).fetchone()
                assert result is not None


class DowngradeTester:
    """Enum tables do not exist."""

    def __init__(self, homedir: str, session: scoped_session) -> None:
        subprocess.check_call(["sqlite3", os.path.join(homedir, "svs.sqlite"), ".databases"])
        self.session = session

    def load_data(self):
        pass

    def check_downgrade(self):
        for table in ENUMS:
            with pytest.raises(OperationalError):
                self.session.execute(text(f"SELECT name FROM {table}"))  # noqa: S608
