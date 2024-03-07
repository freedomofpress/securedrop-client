import os
from unittest.mock import patch

from securedrop_client.config import Config


@patch.dict(os.environ, {"SD_SUBMISSION_KEY_FPR": ""})
def test_missing_journalist_key_fpr():
    """
    If a key is missing, the config can still be loaded, but is "invalid".
    """
    config = Config.load()

    assert config.journalist_key_fingerprint is None
    assert config.is_valid is False
