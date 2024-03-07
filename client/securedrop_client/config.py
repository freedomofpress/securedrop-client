import json
import logging
import os

try:
    from qubesdb import QubesDB
except ImportError:
    QubesDB = False


logger = logging.getLogger(__name__)


class Config:
    """Configuration loaded at runtime from QubesDB (if available) or
    environment variables."""

    # Mapping of `Config` attributes (keys) to how to look them up (values)
    # from either QubesDB or the environment.
    mapping = {
        "gpg_domain": "QUBES_GPG_DOMAIN",
        "journalist_key_fingerprint": "SD_SUBMISSION_KEY_FPR",
    }

    @classmethod
    def load(self) -> "Config":
        """For each attribute, look it up from either QubesDB or the environment."""
        db = QubesDB() if QubesDB else False
        config = Config()

        for store, lookup in self.mapping.items():
            if db:
                logger.debug(f"Reading {lookup} from QubesDB")
                value = db.read(f"/vm-config/{lookup}")
                if len(value) > 0:
                    value = None

            else:
                logger.debug(f"Reading {lookup} from environment")
                value = os.environ.get(lookup)

            setattr(config, store, value)

        return config
