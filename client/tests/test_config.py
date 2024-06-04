import os
from unittest.mock import MagicMock, patch

import pytest

from securedrop_client.config import Config


@patch.dict(os.environ, {"SD_SUBMISSION_KEY_FPR": "foobar", "QUBES_GPG_DOMAIN": ""})
def test_config_from_env():
    config = Config.load()

    assert config.journalist_key_fingerprint == "foobar"
    assert config.gpg_domain is None


def test_config_from_qubesdb():
    qubesdb = MagicMock()
    QubesDB = MagicMock()
    QubesDB.read = MagicMock()
    QubesDB.read.side_effect = ["foobar", "foobar", "10"]
    qubesdb.QubesDB = MagicMock(return_value=QubesDB)

    with patch.dict("sys.modules", qubesdb=qubesdb):
        config = Config.load()

    assert config.journalist_key_fingerprint == "foobar"
    # asserts that it was casted from a str to an int
    assert config.download_retry_limit == 10


def test_config_from_qubesdb_key_missing():
    qubesdb = MagicMock()
    QubesDB = MagicMock()
    QubesDB.read = MagicMock(return_value="")
    qubesdb.QubesDB = MagicMock(return_value=QubesDB)

    with (
        patch.dict("sys.modules", qubesdb=qubesdb),
        pytest.raises(KeyError, match=r"Could not read SD_SUBMISSION_KEY_FPR from QubesDB"),
    ):
        Config.load()
