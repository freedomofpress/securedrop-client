#!/usr/bin/env python3
"""
Verify the reproducibility of gettext machine objects (.mo) from catalogs
(.po).

Due to tool- and library-level idiosyncrasies, this happens in three stages:

1. Via polib: Overwrite metadata .mo → .po.
2. Via translate: Recompile the entire catalog .po → .mo.
3. Via diffoscope: Diff the new .mo against the old, heavily masked and
   filtered to avoid false positives from stray entries in the "fuzzy"
   and "obsolete" states.

In other words, the new .mo file should be identical (modulo stray entries) to
the original, meaning that the original .po/.mo pair differed only in their
metadata.
"""

import argparse
import os
import shlex
import subprocess
from collections.abc import Iterator
from pathlib import Path
from types import TracebackType
from typing import Optional, Set

import polib
from translate.tools.pocompile import convertmo

parser = argparse.ArgumentParser(
    """Verify the reproducibility of gettext machine objects (.mo) from catalogs (.po)."""
)
parser.add_argument(
    "locale",
    nargs="+",
    help="""one or more locale directories, each of which must contain an "LC_MESSAGES" directory""",
)
parser.add_argument(
    "--domain", default="messages", help="""the gettext domain to load (defaults to "messages")"""
)
args = parser.parse_args()


class CatalogVerifier:
    """Wrapper class for proving .mo → .po → .mo reproducibility."""

    def __init__(self, path: Path, domain: str):
        """Set up the .po/.mo pair."""

        self.path = path
        self.po = polib.pofile(str(path / "LC_MESSAGES" / f"{domain}.po"))
        self.mo = polib.mofile(str(path / "LC_MESSAGES" / f"{domain}.mo"))

    def __enter__(self) -> "CatalogVerifier":
        """Prepare to generate the new .mo file to diff."""

        self.mo_target = Path(f"{self.mo.fpath}.new")
        return self

    def __exit__(
        self,
        exc_type: Optional[type[BaseException]],
        exc_value: Optional[BaseException],
        traceback: Optional[TracebackType],
    ) -> None:
        """Clean up."""
        self.mo_target.unlink(missing_ok=True)

    @property
    def diffoscope_args(self) -> Iterator[str]:
        """Build up a diffoscope invocation that removes false positives from the msgunfmt diff."""
        yield f"diffoscope {self.mo.fpath} {self.mo_target}"
        yield "--diff-mask '^$'"  # tell diffoscope to mask empty lines
        for stray in self.strays:
            yield f"--diff-mask {shlex.quote(stray)}"  # tell diffoscope to mask strays
        yield "| grep -Fv '[masked]'"  # ignore things we've masked
        yield "| grep -E '│ (-|\+)msg(id|str)'"  # ignore context; we only care about real diffs

    @property
    def diffoscope_cmd(self) -> str:
        """Return `diffoscope_args` as a string."""
        return " ".join(self.diffoscope_args)

    @property
    def strays(self) -> Set[str]:
        """Return the set of stray (fuzzy or obsolete) entries to mask when
        diffing this catalog."""

        fuzzy = {
            f"^{line.replace('#| ', '')}"  # strip fuzzy marker
            for e in self.po.fuzzy_entries()
            for line in str(e).splitlines()
        }
        obsolete = {
            f"^{line.replace('#~ ', '')}"  # strip obsolete marker
            for e in self.po.obsolete_entries()
            for line in str(e).splitlines()
        }

        return fuzzy | obsolete

    def reproduce(self) -> None:
        """Overwrite metadata .mo → .po.  Then rewrite the entire file .po →
        .mo."""

        self.po.metadata = self.mo.metadata
        self.po.save(self.po.fpath)

        with open(self.mo_target, "wb") as mo_target:
            convertmo(self.po.fpath, mo_target, "")

    def verify(self) -> None:
        """Run diffoscope for this catalog and error if there's any unmasked
        diff."""
        # We silence Bandit and Semgrep warnings on `shell=True`
        # because we want to inherit the Python virtual environment
        # in which we're invoked.
        result = subprocess.run(  # nosec B602 nosemgrep: python.lang.security.audit.subprocess-shell-true.subprocess-shell-true
            self.diffoscope_cmd,
            capture_output=True,
            env=os.environ,
            shell=True,
        )
        print(f"--> Verifying {self.path}: {result.args}")
        if len(result.stdout) > 0:
            raise Exception(result.stdout.decode("utf-8"))


print(f"--> Reproducing {len(args.locale)} path(s)")
for path in args.locale:
    locale_dir = Path(path).resolve()
    if not locale_dir.is_dir():
        print(f'--> Skipping "{locale_dir}"')
        continue

    with CatalogVerifier(locale_dir, args.domain) as catalog:
        catalog.reproduce()
        catalog.verify()
