import json
import os
import tarfile
from io import BytesIO
from typing import List


class Archive:
    METADATA_FN = "metadata.json"
    DISK_EXPORT_DIR = "export_data"

    @staticmethod
    def create_archive(
        archive_dir: str, archive_fn: str, metadata: dict, filepaths: List[str] = []
    ) -> str:
        """
        Create the archive to be sent to the Export VM.

        Args:
            archive_dir (str): The path to the directory in which to create the archive.
            archive_fn (str): The name of the archive file.
            metadata (dict): The dictionary containing metadata to add to the archive.
            filepaths (List[str]): The list of files to add to the archive.

        Returns:
            str: The path to newly-created archive file.
        """
        archive_path = os.path.join(archive_dir, archive_fn)

        with tarfile.open(archive_path, "w:gz") as archive:
            Archive._add_virtual_file_to_archive(archive, Archive.METADATA_FN, metadata)

            for filepath in filepaths:
                Archive._add_file_to_archive(archive, filepath)

        return archive_path

    @staticmethod
    def _add_virtual_file_to_archive(
        archive: tarfile.TarFile, filename: str, filedata: dict
    ) -> None:
        """
        Add filedata to a stream of in-memory bytes and add these bytes to the archive.

        Args:
            archive (TarFile): The archive object to add the virtual file to.
            filename (str): The name of the virtual file.
            filedata (dict): The data to add to the bytes stream.

        """
        filedata_string = json.dumps(filedata)
        filedata_bytes = BytesIO(filedata_string.encode("utf-8"))
        tarinfo = tarfile.TarInfo(filename)
        tarinfo.size = len(filedata_string)
        archive.addfile(tarinfo, filedata_bytes)

    @staticmethod
    def _add_file_to_archive(archive: tarfile.TarFile, filepath: str) -> None:
        """
        Add the file to the archive. When the archive is extracted, the file should exist in a
        directory called "export_data".

        Args:
            archive: The archive object ot add the file to.
            filepath: The path to the file that will be added to the supplied archive.
        """
        filename = os.path.basename(filepath)
        arcname = os.path.join(Archive.DISK_EXPORT_DIR, filename)
        archive.add(filepath, arcname=arcname, recursive=False)
