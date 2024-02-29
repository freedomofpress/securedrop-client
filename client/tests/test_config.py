import os
from unittest.mock import MagicMock, patch

import pytest

from securedrop_client.config import Config


@patch.dict(os.environ, {"SD_SUBMISSION_KEY_FPR": "foobar"})
def test_config_from_env():
    config = Config.load()

    assert config.journalist_key_fingerprint == "foobar"
    assert config.gpg_domain is None


def test_config_from_qubesdb():
    qubesdb = MagicMock()
    QubesDB = MagicMock()
    QubesDB.read = MagicMock(return_value="foobar")
    qubesdb.QubesDB = MagicMock(return_value=QubesDB)

    with patch.dict("sys.modules", qubesdb=qubesdb):
        config = Config.load()

    assert config.journalist_key_fingerprint == "foobar"


def test_config_from_qubesdb_key_missing():
    qubesdb = MagicMock()
    QubesDB = MagicMock()
    QubesDB.read = MagicMock(return_value="")
    qubesdb.QubesDB = MagicMock(return_value=QubesDB)

    with (
        patch.dict("sys.modules", qubesdb=qubesdb),
        pytest.raises(KeyError, match=r"Could not read from QubesDB"),
    ):
        Config.load()
