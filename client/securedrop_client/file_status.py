from enum import Enum


class FileStatus(Enum):
    DOWNLOAD_STARTED = 1
    READY = 2
    MISSING = 3
