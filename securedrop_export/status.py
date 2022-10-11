from enum import Enum


class BaseStatus(Enum):
    """
    Base class for export and print statuses. A Status represents a string that can be returned
    to the calling VM via stderr to provide diagnostic information about the success of a call.
    Status values are defined in subclasses in their respective packages. A full list is available
    in the project's README.
    """

    pass
