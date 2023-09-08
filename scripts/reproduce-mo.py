#!/usr/bin/env python3
"""
Reproduce gettext machine objects (.mo) from catalogs (.po).

Due to tool- and library-level idiosyncrasies, this happens in two
stages:

1. Via polib: Overwrite metadata .mo → .po.
2. Via translate: Rewrite the entire file .po → .mo.

The final .mo file should be unchanged from the original, meaning
that the original .po/.mo pair differed only in their metadata.
"""
import argparse
from pathlib import Path

import polib
from translate.tools.pocompile import convertmo

parser = argparse.ArgumentParser("""Reproduce gettext machine objects (.mo) from catalogs (.po).""")
parser.add_argument(
    "locale",
    nargs="+",
    help="""one or more locale directories, each of which must contain an "LC_MESSAGES" directory""",
)
parser.add_argument(
    "--domain", default="messages", help="""the gettext domain to load (defaults to "messages")"""
)
args = parser.parse_args()


class Locale:
    """Wrapper class for proving .mo → .po → .mo reproducibility."""

    def __init__(self, path: Path, domain: str):
        """Set up the .po/.mo pair."""
        self.po = polib.pofile(str(path / "LC_MESSAGES" / f"{domain}.po"))
        self.mo = polib.mofile(str(path / "LC_MESSAGES" / f"{domain}.mo"))

    def reproduce(self) -> None:
        """Overwrite metadata .mo → .po.  Then rewrite the entire file .po → .mo."""
        self.po.metadata = self.mo.metadata
        self.po.save(self.po.fpath)

        # convertmo() expects `mo` to be a file object.  Without mypy we get
        # that for free from Path, but we have to set it up manually here since
        # polib.{mo,po}file are typed only to accept a string.
        with open(self.mo.fpath, "wb") as mo:
            convertmo(self.po.fpath, mo, "")


print(f"Reproducing {len(args.locale)} path(s)")
for path in args.locale:
    locale_dir = Path(path).resolve()
    if not locale_dir.is_dir():
        print(f'Skipping "{locale_dir}"')
        continue

    locale = Locale(locale_dir, args.domain)
    locale.reproduce()
