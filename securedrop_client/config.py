import json
import os


class Config:

    CONFIG_NAME = 'config.json'

    def __init__(self, journalist_key_fingerprint: str) -> None:
        self.journalist_key_fingerprint = journalist_key_fingerprint

    @classmethod
    def from_home_dir(cls, sdc_home: str):
        full_path = os.path.join(sdc_home, cls.CONFIG_NAME)
        with open(full_path) as f:
            json_config = json.loads(f.read())
        return Config(
            journalist_key_fingerprint=json_config['journalist_key_fingerprint'],
        )
