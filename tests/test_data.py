"""
Make sure the Data object (which abstracts access to the `/data/`
storage directory) works as expected.
"""
from securedrop_client.data import Data


def test_Data_init(homedir):
    """
    Ensure the Data class instantiates as expected
    """
    data = Data(homedir)
    assert data.data_dir == homedir


def test_Data_file_not_found(homedir):
    """
    Ensure the data class handles missing files gracefully
    (e.g. if the file gets deleted)
    """
    data = Data(homedir)
    msg = data.get('my-file.gpg')

    # No unhandled exceptions should occur, and a 'nice' msg
    # should be shown.
    assert msg == "<Content deleted>"
