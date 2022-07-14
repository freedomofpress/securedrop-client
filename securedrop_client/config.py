import json
import logging
import os

logger = logging.getLogger(__name__)


class Config:

    CONFIG_NAME = "config.json"

    def __init__(self, journalist_key_fingerprint: str) -> None:
        self.journalist_key_fingerprint = journalist_key_fingerprint

    @classmethod
    def from_home_dir(cls, sdc_home: str) -> "Config":
        full_path = os.path.join(sdc_home, Config.CONFIG_NAME)

        try:
            with open(full_path) as f:
                json_config = json.loads(f.read())
        except Exception as e:
            logger.error("Error opening config file at {}: {}".format(full_path, e))
            json_config = {}

        return Config(
            journalist_key_fingerprint=json_config.get("journalist_key_fingerprint", None)
        )

    @property
    def is_valid(self) -> bool:
        return self.journalist_key_fingerprint is not None
