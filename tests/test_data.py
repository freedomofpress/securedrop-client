"""
Make sure the Data object (which abstracts access to the `/data/`
storage directory) works as expected.
"""

from securedrop_client.data import Data

def test_Data_init(tmpdir):
    """
    Ensure the Data class instantiates as expected
    """
    data = Data(tmpdir)
    assert data.data_dir == tmpdir
