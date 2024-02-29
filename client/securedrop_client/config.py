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

    def __init__(self) -> None:
        """For each attribute, look it up from either QubesDB or the environment
        and save it to the internal `config` dictionary."""
        self.config = {}

        for store, lookup in self.mapping.items():
            if QubesDB:
                db = QubesDB()
                logger.debug(f"Reading {lookup} from QubesDB")
                value = db.read(f"/vm-config/{lookup}")

            else:
                logger.debug(f"Reading {lookup} from environment")
                value = os.environ.get(lookup)

            # Handle `None` values explicitly, since QubesDB.read() has no
            # equivalent of dict.get()'s default value.
            if value is not None and len(value) > 0:
                setattr(self, store, value)
            else:
                setattr(self, store, None)

    @property
    def is_valid(self) -> bool:
        return self.journalist_key_fingerprint is not None
