#!/usr/bin/env python3

import abc
import datetime
import json
import logging
import os
import shutil
import subprocess
import sys
import tempfile

from securedrop_export.enums import Command
from securedrop_export.exceptions import ExportStatus
from securedrop_export.utils import safe_extractall

logger = logging.getLogger(__name__)


class Metadata(object):
    """
    Object to parse, validate and store json metadata from the sd-export archive.
    """

    METADATA_FILE = "metadata.json"

    SUPPORTED_ENCRYPTION_METHODS = ["luks"]

    def __init__(self, archive_path):
        # Calling create_and_validate() is the preferred way to initialize
        self.metadata_path = os.path.join(archive_path, self.METADATA_FILE)

    @staticmethod
    def create_and_validate(cls, archive_path) -> 'Metadata':
        """
        Create and validate metadata object. Raise ExportException for invalid metadata.
        """
        md = cls(archive_path)

        try:
            with open(md.metadata_path) as f:
                logger.info("Parsing archive metadata")
                json_config = json.loads(f.read())
                md.export_method = json_config.get("device", None)
                md.encryption_method = json_config.get("encryption_method", None)
                md.encryption_key = json_config.get("encryption_key", None)
                logger.info(
                    "Exporting to device {} with encryption_method {}".format(
                        md.export_method, md.encryption_method
                    )
                )

        # Validate metadata - this will fail if command is not in list of supported commands
        md.command = Commmand.value_of(md.export_method)
        if md.command is Commmand.EXPORT and not md.encryption_method in md.SUPPORTED_ENCRYPTION_METHODS:
            logger.error("Unsuported encryption method")
            raise ExportException(ExportStatus.ERROR_ARCHIVE_METADATA)

        except Exception as ex:
            logger.error("Metadata parsing failure")
            raise ExportException(ExportStatus.ERROR_METADATA_PARSING) from ex

        return md


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
            raise ExportException(ExportStatus.ERROR_EXTRACTION) from ex

    