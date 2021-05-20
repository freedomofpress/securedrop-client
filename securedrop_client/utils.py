import gzip
import logging
import math
import os
import shutil
import time
from contextlib import contextmanager
from pathlib import Path
from typing import IO, Any, BinaryIO, Dict, Generator, Optional, Union

from sqlalchemy.orm.session import Session

from securedrop_client import db


def humanize_filesize(filesize: int) -> str:
    """
    Returns a human readable string of a filesize
    (with an input unit of bytes)
    """
    if filesize < 1024:
        return "{}B".format(str(filesize))
    elif filesize < 1024 * 1024:
        return "{}KB".format(math.floor(filesize / 1024))
    else:
        return "{}MB".format(math.floor(filesize / 1024 ** 2))


@contextmanager
def chronometer(logger: logging.Logger, description: str) -> Generator:
    """
    Measures the execution time of its block.
    """
    try:
        start = time.perf_counter()
        yield
    finally:
        elapsed = time.perf_counter() - start
        logger.info(f"{description} duration: {elapsed:.4f}s")


class SourceCache(object):
    """
    Caches Sources by UUID.
    """

    def __init__(self, session: Session) -> None:
        super().__init__()
        self.cache: Dict[str, db.Source] = {}
        self.session = session

    def get(self, source_uuid: str) -> Optional[db.Source]:
        if source_uuid not in self.cache:
            source = self.session.query(db.Source).filter_by(uuid=source_uuid).first()
            self.cache[source_uuid] = source
        return self.cache.get(source_uuid)
