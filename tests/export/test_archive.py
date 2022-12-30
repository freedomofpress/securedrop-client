import os
import tarfile
import unittest
from tempfile import NamedTemporaryFile, TemporaryDirectory
from unittest.mock import patch

from securedrop_client.export.archive import Archive


class TestExportServiceArchive(unittest.TestCase):
    def test_create_archive_creates_an_archive_with_files(self):

        with TemporaryDirectory() as temp_dir:
            with NamedTemporaryFile() as example_file:
                example_file.write(b"Hello, world!")

                print(example_file.name)
                archive_path = Archive.create_archive(
                    temp_dir, "archive_function", "metadata", [example_file.name]
                )
                print(archive_path)

                with tarfile.open(archive_path, "r:gz") as archive:
                    example_file_name = os.path.basename(example_file.name)
                    expected_archive_content = ["metadata.json", f"export_data/{example_file_name}"]

                    self.assertEqual(expected_archive_content, archive.getnames())

    @patch.object(tarfile, "open")
    def test_create_archive_returns_the_archive_path(self, _):
        expected_archive_path = "directory/archive_function"

        return_value = Archive.create_archive("directory", "archive_function", "metadata")
        self.assertEqual(expected_archive_path, return_value)
