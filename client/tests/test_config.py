import os

from securedrop_client.config import Config


def test_missing_file(homedir):
    """
    If a file doesn't exist, the config can still be created, but is "invalid".
    """
    # precondition
    assert not os.path.exists(os.path.join(homedir, Config.CONFIG_NAME))

    config = Config.from_home_dir(homedir)

    assert config.journalist_key_fingerprint is None
    assert config.is_valid is False


def test_missing_journalist_key_fpr(homedir):
    """
    If a key is missing, the config can still be created, but is "invalid".
    """
    config_path = os.path.join(homedir, Config.CONFIG_NAME)
    with open(config_path, "w") as f:
        f.write("{}")

    config = Config.from_home_dir(homedir)

    assert config.journalist_key_fingerprint is None
    assert config.is_valid is False
