import gzip
import struct

import pytest

from securedrop_client.crypto import (
    GZIP_FILE_IDENTIFICATION,
    GZIP_FLAG_EXTRA_FIELDS,
    GZIP_FLAG_FILENAME,
    read_gzip_header_filename,
)

GZIP_COMPRESSION_BYTES = b"\010"


def test_gzip_file_with_filename(tmp_path):
    """Test extracting filename from a gzip file that has a filename in header."""
    tmp_file = tmp_path / "test.gz"
    original_name = "test_file.txt"

    # Create a gzip file with a filename in the header
    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method (8 = deflate)
        f.write(bytes([GZIP_FLAG_FILENAME]))  # Flags with FNAME set
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        f.write(original_name.encode("utf-8") + b"\000")  # Filename + null terminator
        # Compress and write data
        f.write(gzip.compress(b"test content")[10:])  # Skip gzip header

    result = read_gzip_header_filename(str(tmp_file))
    assert result == original_name


def test_gzip_file_without_filename(tmp_path):
    """Test extracting filename from a gzip file without filename in header."""
    tmp_file = tmp_path / "test.gz"

    # Create a gzip file without filename flag
    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method
        f.write(b"\000")  # Flags (no FNAME)
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        f.write(gzip.compress(b"test content")[10:])  # Skip gzip header

    result = read_gzip_header_filename(str(tmp_file))
    assert result == ""


def test_gzip_file_with_extra_fields(tmp_path):
    """Test extracting filename from a gzip file with extra fields."""
    tmp_file = tmp_path / "test.gz"
    original_name = "extra_test.dat"

    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method
        flags = GZIP_FLAG_EXTRA_FIELDS | GZIP_FLAG_FILENAME
        f.write(bytes([flags]))  # Flags
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        # Extra fields
        extra_data = b"EXTRA"
        f.write(struct.pack("<H", len(extra_data)))  # Extra length
        f.write(extra_data)
        # Filename
        f.write(original_name.encode("utf-8") + b"\000")
        f.write(gzip.compress(b"test content")[10:])

    result = read_gzip_header_filename(str(tmp_file))
    assert result == original_name


def test_not_gzip_file(tmp_path):
    """Test that non-gzip file raises OSError."""
    tmp_file = tmp_path / "not_gzip.txt"
    tmp_file.write_bytes(b"This is not a gzip file")

    with pytest.raises(OSError, match="Not a gzipped file"):
        read_gzip_header_filename(str(tmp_file))


def test_unknown_compression_method(tmp_path):
    """Test that unknown compression method raises OSError."""
    tmp_file = tmp_path / "test.gz"

    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(b"\099")  # Invalid compression method
        f.write(b"\000")  # Flags
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000\000")  # XFL, OS

    with pytest.raises(OSError, match="Unknown compression method"):
        read_gzip_header_filename(str(tmp_file))


def test_unicode_filename(tmp_path):
    """Test extracting unicode filename from gzip header."""
    tmp_file = tmp_path / "test.gz"
    original_name = "测试文件.txt"

    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method
        f.write(bytes([GZIP_FLAG_FILENAME]))  # Flags
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        f.write(original_name.encode("utf-8") + b"\000")
        f.write(gzip.compress(b"test content")[10:])

    result = read_gzip_header_filename(str(tmp_file))
    assert result == original_name


def test_empty_filename(tmp_path):
    """Test gzip file with filename flag but empty filename."""
    tmp_file = tmp_path / "test.gz"

    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method
        f.write(bytes([GZIP_FLAG_FILENAME]))  # Flags
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        f.write(b"\000")  # Just null terminator (empty filename)
        f.write(gzip.compress(b"test content")[10:])

    result = read_gzip_header_filename(str(tmp_file))
    assert result == ""


def test_path_traversal(tmp_path):
    """Test a path traversal is rejected."""
    tmp_file = tmp_path / "test.gz"
    original_name = "../../../../../etc/passwd"

    with open(tmp_file, "wb") as f:
        f.write(GZIP_FILE_IDENTIFICATION)  # ID
        f.write(GZIP_COMPRESSION_BYTES)  # Compression method
        f.write(bytes([GZIP_FLAG_FILENAME]))  # Flags
        f.write(b"\000\000\000\000")  # mtime
        f.write(b"\000")  # XFL
        f.write(b"\377")  # OS
        f.write(original_name.encode("utf-8") + b"\000")
        f.write(gzip.compress(b"test content")[10:])

    with pytest.raises(
        ValueError, match="Unsafe file or directory name: '../../../../../etc/passwd'"
    ):
        read_gzip_header_filename(str(tmp_file))
