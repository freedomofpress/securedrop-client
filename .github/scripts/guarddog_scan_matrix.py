#!/usr/bin/env python3
"""Build the GuardDog scan matrix from a git-pkgs diff.

Reads `git pkgs diff -f json` on stdin, groups npm / PyPI / GitHub Actions
additions and upgrades by ecosystem, and writes one GuardDog input manifest per
group. It prints a JSON array on stdout that becomes the GitHub Actions job
matrix, so one scan job is spawned per generated manifest.

Each emitted object has:
  scanner    GuardDog scan subcommand to run (npm, pypi, github_action)
  path       repository-relative path to the generated input manifest
  category   unique GitHub code-scanning category for this ecosystem

See: https://developers.securedrop.org/en/latest/dependency_updates.html
"""

import argparse
import json
import os
import sys
from collections import Counter
from collections.abc import Callable
from pathlib import Path

# git-pkgs ecosystem name -> (GuardDog scan subcommand, manifest kind to scan).
# Note the strings differ on both sides for Actions: git-pkgs says
# "github-actions", GuardDog's subcommand is "github_action". Ecosystems
# GuardDog can't scan (cargo, ...) aren't in this map and are reported as
# skipped.
ECOSYSTEMS = {
    "npm": ("npm", "lockfile"),
    "pypi": ("pypi", "lockfile"),
    "github-actions": ("github_action", "manifest"),
}

MANIFEST_NAMES = {
    "npm": "package.json",
    "pypi": "requirements.txt",
    "github_action": "workflow.yml",
}


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
            # to_requirement is the *new* requirement for both added and
            # modified entries; that is what we want to scan.
            version = entry.get("to_requirement", "")
            kind = ECOSYSTEMS.get(ecosystem, (None, None))[1]
            if kind is not None and entry.get("manifest_kind") != kind:
                continue
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


def render_npm(dependencies: list[dict[str, str]]) -> str:
    """Render exact npm versions, using aliases if a package appears twice."""
    name_counts = Counter(dependency["name"] for dependency in dependencies)
    manifest_dependencies = {}
    for index, dependency in enumerate(dependencies):
        name = dependency["name"]
        version = dependency["version"]
        if name_counts[name] == 1:
            manifest_dependencies[name] = version
        else:
            manifest_dependencies[f"guarddog-dependency-{index}"] = f"npm:{name}@{version}"
    return json.dumps({"private": True, "dependencies": manifest_dependencies}, indent=2) + "\n"


def render_pypi(dependencies: list[dict[str, str]]) -> str:
    """Render exact PyPI requirements."""
    return "".join(
        f"{dependency['name']}=={dependency['version']}\n" for dependency in dependencies
    )


def render_github_actions(dependencies: list[dict[str, str]]) -> str:
    """Render a synthetic workflow containing each exact action reference."""
    workflow = {
        "name": "GuardDog dependency verification",
        "on": "workflow_dispatch",
        "jobs": {
            "verify": {
                "runs-on": "ubuntu-latest",
                "steps": [
                    {"uses": f"{dependency['name']}@{dependency['version']}"}
                    for dependency in dependencies
                ],
            }
        },
    }
    # GuardDog parses workflows with yaml.safe_load(), which accepts JSON syntax.
    return json.dumps(workflow, indent=2) + "\n"


RENDERERS: dict[str, Callable[[list[dict[str, str]]], str]] = {
    "npm": render_npm,
    "pypi": render_pypi,
    "github_action": render_github_actions,
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path, required=True)
    args = parser.parse_args()
    args.output_directory.mkdir(parents=True, exist_ok=True)

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
    skipped = [p for p in packages if p["ecosystem"] not in ECOSYSTEMS]
    groups = []
    for ecosystem, (scanner, _) in ECOSYSTEMS.items():
        dependencies = [
            {
                "name": p["name"],
                "version": p["version"],
                "change": p["change"],
            }
            for p in packages
            if p["ecosystem"] == ecosystem
        ]
        if dependencies:
            groups.append(
                {
                    "ecosystem": ecosystem,
                    "scanner": scanner,
                    "dependencies": dependencies,
                    "category": f"guarddog/{ecosystem}",
                }
            )

    step_summary("## GuardDog dependency scan")
    step_summary()
    manifests = []
    if groups:
        for group in groups:
            step_summary(f"Spawning a scan job for {group['ecosystem']} package(s):")
            step_summary()
            for p in group["dependencies"]:
                step_summary(f"- `{p['name']}` ({p['version']}, {p['change']})")
            step_summary()

            manifest = args.output_directory / MANIFEST_NAMES[group["scanner"]]
            manifest.write_text(
                RENDERERS[group["scanner"]](group["dependencies"]), encoding="utf-8"
            )
            manifests.append(
                {
                    "category": group["category"],
                    "scanner": group["scanner"],
                    "path": manifest.as_posix(),
                }
            )
    else:
        step_summary("No npm/PyPI/Actions additions or upgrades to scan. ✅")
    if skipped:
        others = ", ".join(sorted({p["ecosystem"] for p in skipped}))
        step_summary(f"\n_Skipped unsupported ecosystems: {others}._")

    # stdout: only the matrix, so the workflow can capture it cleanly.
    print(json.dumps(manifests))

    return 0


if __name__ == "__main__":
    sys.exit(main())
