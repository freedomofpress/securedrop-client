"""
Make sure the Data object (which abstracts access to the `/data/`
storage directory) works as expected.
"""
from securedrop_client.data import Data


def test_Data_init(safe_tmpdir):
    """
    Ensure the Data class instantiates as expected
    """
    data = Data(str(safe_tmpdir))
    assert data.data_dir == safe_tmpdir


def test_Data_file_not_found(safe_tmpdir):
    """
    Ensure the data class handles missing files gracefully
    (e.g. if the file gets deleted)
    """
    data = Data(str(safe_tmpdir))
    msg = data.get('my-file.gpg')

    # No unhandled exceptions should occur, and a 'nice' msg
    # should be shown.
    assert msg == "<Content deleted>"
