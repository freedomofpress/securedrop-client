#!/usr/bin/env python3

import datetime
import json
import logging
import os
import shutil
import subprocess
import sys
import tempfile

from securedrop_export.exceptions import ExportException
from securedrop_export.status import BaseStatus
from securedrop_export.command import Command
from securedrop_export.directory_util import safe_extractall

logger = logging.getLogger(__name__)

class Status(BaseStatus):
    ERROR_ARCHIVE_METADATA = "ERROR_ARCHIVE_METADATA"
    ERROR_METADATA_PARSING = "ERROR_METADATA_PARSING"
    ERROR_EXTRACTION = "ERROR_EXTRACTION"

class Metadata(object):
    """
    Object to parse, validate and store json metadata from the sd-export archive.

    Create a Metadata object by using the `create_and_validate()` method to
    ensure well-formed and valid metadata.
    """

    METADATA_FILE = "metadata.json"
    SUPPORTED_ENCRYPTION_METHODS = ["luks"]

    # Slightly underhanded way of ensuring that a Metadata object is not instantiated
    # directly; instead, the create_and_validate() method is used
    __key = object()


    def __init__(self, key: object, archive_path: str):
        if not key == Metadata.__key:
            raise ValueError("Must use create_and_validate() to create Metadata object")

        # Initialize
        self.metadata_path = os.path.join(archive_path, self.METADATA_FILE)


    @classmethod
    def create_and_validate(cls, archive_path) -> 'Metadata':
        """
        Create and validate metadata object. Raise ExportException for invalid metadata.
        """
        md = Metadata(cls.__key, archive_path)
        md.validate()

        return md


    def validate(self):
        """
        Validate Metadata.
        Throw ExportException if invalid state is found.
        """
        try:
            with open(self.metadata_path) as f:
                logger.info("Parsing archive metadata")
                json_config = json.loads(f.read())
                self.export_method = json_config.get("device", None)
                self.encryption_method = json_config.get("encryption_method", None)
                self.encryption_key = json_config.get("encryption_key", None)
                logger.info(
                    "Exporting to device {} with encryption_method {}".format(
                        self.export_method, self.encryption_method
                    )
                )

        except Exception as ex:
            logger.error("Metadata parsing failure")
            raise ExportException(sdstatus=Status.ERROR_METADATA_PARSING) from ex

        # Validate metadata - this will fail if command is not in list of supported commands
        try:        
            self.command = Command(self.export_method)
            if self.command is Command.EXPORT and not self.encryption_method in self.SUPPORTED_ENCRYPTION_METHODS:
                logger.error("Unsupported encryption method")
                raise ExportException(sdstatus=Status.ERROR_ARCHIVE_METADATA)
        except ValueError as v:
            raise ExportException(sdstatus=Status.ERROR_METADATA_PARSING) from v


class Archive(object):
    def __init__(self, archive, config_path):
        os.umask(0o077)
        self.archive = archive
        self.submission_dirname = os.path.basename(self.archive).split(".")[0]
        self.target_dirname = "sd-export-{}".format(
            datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        )
        self.tmpdir = tempfile.mkdtemp()

    def extract_tarball(self):
        try:
            logger.info("Extracting tarball {} into {}".format(self.archive, self.tmpdir))
            safe_extractall(self.archive, self.tmpdir)
        except Exception as ex:
            logger.error("Unable to extract tarball: {}".format(ex))
            raise ExportException(sdstatus=Status.ERROR_EXTRACTION) from ex

    