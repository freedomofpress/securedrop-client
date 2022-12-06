import tarfile
import unittest
from unittest.mock import patch

from securedrop_client.export.archive import Archive


class TestExportServiceArchive(unittest.TestCase):
    @patch.object(tarfile, "open")
    def test_create_archive_returns_the_archive_path(self, _):

        return_value = Archive.create_archive("directory", "archive_function", "metadata")

        self.assertEqual("directory/archive_function", return_value)
