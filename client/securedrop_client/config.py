import logging
import os
from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import MISSING, dataclass, fields

logger = logging.getLogger(__name__)


@contextmanager
def try_qubesdb() -> Generator:
    """Minimal context manager around QubesDB() → QubesDB.close() when
    available."""
    db: bool | "QubesDB" = False  # noqa: UP037

    try:
        from qubesdb import QubesDB

        db = QubesDB()
        yield db

    except ImportError:
        logger.debug("QubesDB not available")
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
        "download_retry_limit": "SD_DOWNLOAD_RETRY_LIMIT",
    }

    journalist_key_fingerprint: str
    gpg_domain: str | None = None
    download_retry_limit: int = 3

    @classmethod
    def load(cls) -> "Config":
        """For each attribute, look it up from either QubesDB or the environment."""
        config = {}

        with try_qubesdb() as db:
            for field in fields(cls):
                lookup = cls.mapping[field.name]
                if db:
                    logger.debug(f"Reading {lookup} from QubesDB")
                    value = db.read(f"/vm-config/{lookup}")
                    if not value or len(value) == 0:
                        if field.default == MISSING:
                            raise KeyError(f"Could not read {lookup} from QubesDB")
                        # Normalize for parity with the case where os.environ.get() is None
                        value = None
                else:
                    logger.debug(f"Reading {lookup} from environment")
                    value = os.environ.get(lookup)
                    if not value or len(value) == 0:
                        # Same normalization used for QubesDB
                        value = None

                if value is None and field.default != MISSING:
                    logger.debug(f"Using default value for {lookup}")
                    value = field.default

                # Cast to int if needed (might raise if value is invalid)
                # TODO: in theory we could `field.type(value)` but that doesn't
                # handle union types
                if field.type is int:
                    value = int(value)
                config[field.name] = value

        return cls(**config)
