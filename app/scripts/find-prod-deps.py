#!/usr/bin/env python3
"""
Find all npm packages actually imported in src/main, src/renderer, and src/preload,
by intersecting with packages listed in package.json.
"""

import json
import re
from pathlib import Path

SEARCH_DIRS = ["src/main", "src/renderer", "src/preload"]

IMPORT_RE = re.compile(
    r"""(?:from\s+|import\s*[\(\s]|require\s*\()['"](@[\w.-]+/[\w.-]+|[\w][\w.-]*)"""
)
# Packages that really aren't prod but the script can't detect that
NOT_PROD = ["electron-devtools-installer"]


def is_test_file(path: Path) -> bool:
    parts = path.parts
    name = path.name
    return "__tests__" in parts or ".test." in name or ".spec." in name or name.startswith("test-")


def find_packages(root: Path, known_packages: set[str]) -> set[str]:
    pkgs: set[str] = set()
    for search_dir in SEARCH_DIRS:
        for ts_file in [*(root / search_dir).rglob("*.ts"), *(root / search_dir).rglob("*.tsx")]:
            if is_test_file(ts_file):
                continue
            text = ts_file.read_text()
            for match in IMPORT_RE.findall(text):
                if match in known_packages and match not in NOT_PROD:
                    pkgs.add(match)
    return pkgs


if __name__ == "__main__":
    root = Path(__file__).parent.parent
    pkg_json = json.loads((root / "package.json").read_text())
    known = set(pkg_json["dependencies"]) | set(pkg_json["devDependencies"])

    packages = find_packages(root, known)
    for pkg in sorted(packages):
        print(pkg)
