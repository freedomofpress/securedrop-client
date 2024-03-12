import os
from unittest.mock import patch

from securedrop_client.config import Config


@patch.dict(os.environ, {"SD_SUBMISSION_KEY_FPR": "foobar"})
def test_config():
    """
    If a key is missing, the config can still be loaded, but is "invalid".
    """
    config = Config.load()

    assert config.journalist_key_fingerprint == "foobar"
    assert config.gpg_domain is None
