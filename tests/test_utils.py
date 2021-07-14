import os
import tempfile
from pathlib import Path

import pytest

from securedrop_client.utils import (
    humanize_filesize,
)


def test_humanize_file_size_bytes():
    expected_humanized_filesize = "123B"
    actual_humanized_filesize = humanize_filesize(123)
    assert expected_humanized_filesize == actual_humanized_filesize


def test_humanize_file_size_kilobytes():
    expected_humanized_filesize = "123KB"
    actual_humanized_filesize = humanize_filesize(123 * 1024)
    assert expected_humanized_filesize == actual_humanized_filesize


def test_humanize_file_size_megabytes():
    expected_humanized_filesize = "123MB"
    actual_humanized_filesize = humanize_filesize(123 * 1024 * 1024)
    assert expected_humanized_filesize == actual_humanized_filesize
