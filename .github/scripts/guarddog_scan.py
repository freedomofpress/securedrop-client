#!/usr/bin/env python3
"""Build the GuardDog scan matrix from a git-pkgs diff.

Reads `git pkgs diff -f json` on stdin and prints a JSON array on stdout, one
object per npm / PyPI / GitHub Actions add-or-upgrade. That array becomes the
GitHub Actions job matrix, so one scan job is spawned per dependency. The
GuardDog scan itself runs inline in the workflow (see guarddog.yml), so this
script -- and therefore a repo checkout -- is only needed in the discover job.

Each emitted object has:
  ecosystem  git-pkgs ecosystem name (npm, pypi, github-actions) -- for display
  scanner    GuardDog scan subcommand to run (npm, pypi, github_action)
  name       package, or owner/repo for an action
  version    resolved version / ref to scan
  change     added | modified

See: https://developers.securedrop.org/en/latest/dependency_updates.html
"""

import json
import os
import sys

# git-pkgs ecosystem name -> GuardDog scan subcommand. Note the strings differ
# on both sides for Actions: git-pkgs says "github-actions", GuardDog's
# subcommand is "github_action". Ecosystems GuardDog can't scan (cargo, ...)
# aren't in this map and are reported as skipped.
ECOSYSTEMS = {"npm": "npm", "pypi": "pypi", "github-actions": "github_action"}


def step_summary(line: str = "") -> None:
    """Append a line to the GitHub Actions job summary (and the log on stderr).

    Writes to stderr (not stdout) so stdout stays reserved for the matrix JSON.
    """
    print(line, file=sys.stderr)
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")


def normalize_github_action(name: str) -> str | None:
    """Reduce a `uses:` reference to the `owner/repo` GuardDog can scan.

    git-pkgs may include a subpath (e.g. `github/codeql-action/upload-sarif`),
    but GuardDog scans the whole repo and only accepts `owner/repo`. Local
    (`./...`) and `docker://` actions can't be fetched from GitHub, so they are
    dropped (return None).
    """
    if name.startswith(".") or "://" in name:
        return None
    parts = name.split("/")
    if len(parts) < 2:
        return None
    return "/".join(parts[:2])


def collect_packages(diff: dict) -> list[dict]:
    """Pull added + modified entries from a git-pkgs diff, deduped."""
    seen: set[tuple[str, str, str]] = set()
    packages: list[dict] = []
    for change in ("added", "modified"):
        for entry in diff.get(change, []):
            ecosystem = entry.get("ecosystem", "")
            name = entry.get("name", "")
            # to_requirement is the *new* resolved version for both added and
            # modified entries; that is what we want to scan.
            version = entry.get("to_requirement", "")
            if ecosystem == "github-actions":
                # Collapse subpaths to owner/repo (and drop local/docker
                # actions) so GuardDog can scan them and so two actions from the
                # same repo dedupe to a single scan.
                name = normalize_github_action(name)
                if name is None:
                    continue
            key = (ecosystem, name, version)
            if not name or not version or key in seen:
                continue
            seen.add(key)
            packages.append(
                {
                    "ecosystem": ecosystem,
                    "name": name,
                    "version": version,
                    "change": change,
                }
            )
    return packages


def main() -> int:
    raw = sys.stdin.read().strip()
    # With nothing to compare, git-pkgs prints this sentinel even with -f json.
    if not raw or raw == "No dependency changes.":
        step_summary("## GuardDog dependency scan\n\nNo dependency changes. ✅")
        print("[]")
        return 0
    try:
        diff = json.loads(raw)
    except json.JSONDecodeError as exc:
        step_summary(f"Could not parse git-pkgs diff JSON: {exc}")
        print("[]")
        return 1

    packages = collect_packages(diff)
    scannable = [
        {**p, "scanner": ECOSYSTEMS[p["ecosystem"]]}
        for p in packages
        if p["ecosystem"] in ECOSYSTEMS
    ]
    skipped = [p for p in packages if p["ecosystem"] not in ECOSYSTEMS]

    step_summary("## GuardDog dependency scan")
    step_summary()
    if scannable:
        step_summary(f"Spawning a scan job for {len(scannable)} package(s):")
        step_summary()
        for p in scannable:
            step_summary(f"- `{p['name']}` ({p['ecosystem']} {p['version']}, {p['change']})")
    else:
        step_summary("No npm/PyPI/Actions additions or upgrades to scan. ✅")
    if skipped:
        others = ", ".join(sorted({p["ecosystem"] for p in skipped}))
        step_summary(f"\n_Skipped unsupported ecosystems: {others}._")

    # stdout: only the matrix, so the workflow can capture it cleanly.
    print(json.dumps(scannable))
    return 0


if __name__ == "__main__":
    sys.exit(main())
