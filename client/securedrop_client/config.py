import logging
import os
from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass

logger = logging.getLogger(__name__)


@contextmanager
def try_qubesdb() -> Generator:
    """Minimal context manager around QubesDB() → QubesDB.close() when
    available."""
    db: bool | "QubesDB" = False

    try:
        from qubesdb import QubesDB

        db = QubesDB()
        yield db

    except ImportError:
        yield db

    finally:
        if db:
            db.close()  # type: ignore[union-attr]


@dataclass
class Config:
    """Configuration loaded at runtime from QubesDB (if available) or
    environment variables."""

    # Mapping of `Config` attributes (keys) to how to look them up (values)
    # from either QubesDB or the environment.
    mapping = {
        "gpg_domain": "QUBES_GPG_DOMAIN",
        "journalist_key_fingerprint": "SD_SUBMISSION_KEY_FPR",
    }

    gpg_domain: str
    journalist_key_fingerprint: str

    @classmethod
    def load(self) -> "Config":
        """For each attribute, look it up from either QubesDB or the environment."""
        config = {}

        with try_qubesdb() as db:
            for store, lookup in self.mapping.items():
                if db:
                    logger.debug(f"Reading {lookup} from QubesDB")
                    value = db.read(f"/vm-config/{lookup}")
                    if not value or len(value) == 0:
                        raise KeyError(f"Could not read from QubesDB: {lookup}")

                else:
                    logger.debug(f"Reading {lookup} from environment")
                    value = os.environ.get(lookup)

                config[store] = value

        return Config(**config)
