#!/usr/bin/env python3

import datetime
import json
import logging
import os
import tempfile

from securedrop_export.exceptions import ExportException
from securedrop_export.status import BaseStatus
from securedrop_export.command import Command
from securedrop_export.directory import safe_extractall

logger = logging.getLogger(__name__)


class Status(BaseStatus):
    ERROR_ARCHIVE_METADATA = "ERROR_ARCHIVE_METADATA"
    ERROR_METADATA_PARSING = "ERROR_METADATA_PARSING"
    ERROR_EXTRACTION = "ERROR_EXTRACTION"


class Metadata(object):
    """
    Object to parse, validate and store json metadata from the sd-export archive.
    """

    METADATA_FILE = "metadata.json"

    def __init__(self, archive_path: str):
        self.metadata_path = os.path.join(archive_path, self.METADATA_FILE)

    def validate(self) -> "Metadata":
        # Read metadata json and set relevant attributes
        try:
            with open(self.metadata_path) as f:
                logger.info("Parsing archive metadata")
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_key = json_config.get("encryption_key", None)
                self.encryption_method = json_config.get("encryption_method", None) 
                logger.info("Command: {}".format(self.export_method))

        except Exception as ex:
            logger.error("Metadata parsing failure")
            raise ExportException(sdstatus=Status.ERROR_METADATA_PARSING) from ex

        # Validate action - fails if command is not in list of supported commands
        try:
            logger.debug("Validate export action")
            self.command = Command(self.export_method)
        except ValueError as v:
            raise ExportException(sdstatus=Status.ERROR_ARCHIVE_METADATA) from v

        return self


class Archive(object):
    def __init__(self, archive_path: str):
        os.umask(0o077)
        self.archive = archive_path
        self.target_dirname = "sd-export-{}".format(
            datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        )
        self.tmpdir = tempfile.mkdtemp()

    def extract_tarball(self) -> "Archive":
        """
        Extract tarball, checking for path traversal, and return Archive object.
        """
        try:
            logger.info(
                "Extracting tarball {} into {}".format(self.archive, self.tmpdir)
            )
            safe_extractall(self.archive, self.tmpdir)
            return self
        except Exception as ex:
            logger.error("Unable to extract tarball: {}".format(ex))
            raise ExportException(sdstatus=Status.ERROR_EXTRACTION) from ex

    def set_metadata(self, metadata: Metadata) -> "Archive":
        """
        Set relevant metadata attributes for a given archive.
        """
        self.command = metadata.command
        if self.command is Command.EXPORT:
            self.encryption_key = metadata.encryption_key
        return self
