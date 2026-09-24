#!/usr/bin/env python3
"""Scan every npm, PyPI and GitHub Actions dependency with GuardDog and write SARIF.

GuardDog's own SARIF output reports each heuristic match as a separate
`warning`, dropping the aggregate risk score it computes for the package. We
want one alert per dependency version that carries that aggregate assessment,
so this script runs `guarddog <ecosystem> scan --output-format json` for every
dependency version in the repository and converts each assessment into a
single SARIF result so it can be ingested into Github code scanning.

Each result is anchored to the line that pins the version: a `packages:` key in
pnpm-lock.yaml, a `version =` line in poetry.lock, or a workflow `uses:` line.
That way GitHub code scanning shows a new alert on the pull request line that
introduces it. The alert's fingerprint includes the version, so dismissing an
alert accepts only that version, while upgrading produces a new alert.

A version GuardDog can't fully scan gets a high-severity "incomplete" alert
instead of failing the job, so that it is reviewed and dismissed the same way.
The script fails if GuardDog can't run or assesses nothing, and when a lockfile
pins a dependency it can't hand to GuardDog, such as a Poetry git dependency,
rather than scan something else in its place.

See: https://developers.securedrop.org/en/latest/dependency_updates.html
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

import yaml

NO_RISK = "no_risks_detected"
INCOMPLETE = "incomplete"

# Rule ID -> (SARIF level, GitHub security-severity, description). The first
# three IDs are GuardDog's risk labels. Their security-severity is the lowest
# score GuardDog gives the label, which falls in GitHub's matching band: high
# (7.0-8.9), medium (4.0-6.9), low (0.1-3.9). An incomplete scan may understate
# the risk, so it is treated as high.
RULES = {
    "high_risk": ("error", "7.0", "GuardDog rates this dependency version high_risk"),
    "suspicious": ("warning", "5.0", "GuardDog rates this dependency version suspicious"),
    "low": ("note", "0.1", "GuardDog rates this dependency version low"),
    INCOMPLETE: ("error", "7.0", "GuardDog could not fully assess this dependency version"),
}

HELP = """\
GuardDog combined its heuristic findings for this dependency version into the
risk score shown in the alert. The alert marks the version for manual review;
it is not proof that the package is malicious. If GuardDog hit errors, the
alert lists them, and any score it shows may understate the risk.

Review the flagged files in the package. If the version is acceptable, dismiss
the alert with a comment recording what you checked. The dismissal covers this
version only, while a different version gets a new alert.

The alert's SARIF properties hold GuardDog's score breakdown, every risk it
found, and any errors. Rule documentation:
https://github.com/DataDog/guarddog/blob/v3/RULES.md
"""

# Characters of each GuardDog error to put in an alert message. Tracebacks end
# with the useful part, so the tail is kept.
MAX_ERROR_LENGTH = 500

# Lines of risk evidence to put in an alert message before summarizing the rest.
MAX_RISKS_SHOWN = 10


@dataclass(frozen=True)
class Dependency:
    ecosystem: str  # GuardDog subcommand: npm, pypi or github_action
    name: str
    version: str

    def __str__(self) -> str:
        return f"{self.ecosystem}:{self.name}@{self.version}"


@dataclass(frozen=True, order=True)
class Location:
    path: str
    line: int

    def __str__(self) -> str:
        return f"{self.path}:{self.line}"


def unsupported(location: Location, what: str) -> ValueError:
    return ValueError(
        f"{location}: GuardDog can't scan {what}. "
        "Extend .github/scripts/guarddog_sarif.py before using this kind of dependency."
    )


class YamlString(str):
    """A string from a YAML file that remembers the line it was on."""

    line: int


class LineLoader(yaml.SafeLoader):
    """Load YAML like `yaml.safe_load`, but with every string as a YamlString."""

    def construct_scalar(self, node):
        string = YamlString(super().construct_scalar(node))
        string.line = node.start_mark.line + 1
        return string


def load_yaml(text: str):
    return yaml.load(text, Loader=LineLoader)  # noqa: S506 (LineLoader is a SafeLoader)


def parse_pnpm_lock(path: str, text: str):
    # pnpm-lock.yaml v9 lists every resolved package once under `packages:`,
    # keyed `name@version`.
    for key in load_yaml(text).get("packages", {}):
        location = Location(path, key.line)
        # The name may start with a scope's @, and an archive URL may contain one.
        at = key.find("@", 1)
        name, version = key[:at], key[at + 1 :]
        # A few packages are pinned to an archive URL, which GuardDog scans directly.
        if at < 1 or not (version[:1].isdigit() or version.startswith("https://")):
            raise unsupported(location, key)
        yield Dependency("npm", name, version), location


def parse_poetry_lock(path: str, text: str):
    # tomllib reads the packages. A line scan finds each [[package]] table's own
    # `version =` line to anchor it, since tomllib reports no positions.
    lines, table = [], None
    for number, line in enumerate(text.splitlines(), start=1):
        if line.startswith("["):
            table = line.strip()
        elif table == "[[package]]" and line.startswith("version = "):
            lines.append(number)
    for package, number in zip(tomllib.loads(text).get("package", []), lines, strict=True):
        location = Location(path, number)
        if "source" in package:
            # e.g. a git or path dependency. Scanning the PyPI package of the
            # same name would assess different code.
            raise unsupported(location, f"{package['name']} from a {package['source']['type']}")
        # PEP 503 normalization, so one package never has two identities.
        name = re.sub(r"[-_.]+", "-", package["name"]).lower()
        yield Dependency("pypi", name, package["version"]), location


def parse_workflow(path: str, text: str):
    for job in load_yaml(text)["jobs"].values():
        # A job can call a reusable workflow, and each of its steps an action.
        for step in [job, *job.get("steps", [])]:
            if not (uses := step.get("uses")):
                continue
            location = Location(path, uses.line)
            action, _, ref = uses.partition("@")
            if action.startswith(("./", "docker://")):
                # Local actions are repository code, and GuardDog doesn't scan
                # container images.
                print(f"Skipping {location}: {uses}", file=sys.stderr)
                continue
            if not ref:
                raise unsupported(location, uses)
            # GuardDog scans the whole repository, so drop any subpath
            # (e.g. github/codeql-action/upload-sarif).
            repository = "/".join(action.split("/")[:2])
            yield Dependency("github_action", repository, ref), location


def parser_for(path: str):
    file = PurePosixPath(path)
    if file.name == "pnpm-lock.yaml":
        return parse_pnpm_lock
    if file.name == "poetry.lock":
        return parse_poetry_lock
    if file.parent == PurePosixPath(".github/workflows") and file.suffix in (".yml", ".yaml"):
        return parse_workflow
    return None


def inventory(root: Path, paths: list[str]) -> dict[Dependency, Location]:
    """Map each dependency version to the first line that pins it.

    A version pinned in several places gets one alert, anchored to its first
    location by path and line so that the anchor is stable across runs.
    """
    found: dict[Dependency, Location] = {}
    for path in sorted(paths):
        if parse := parser_for(path):
            for dependency, location in parse(path, (root / path).read_text(encoding="utf-8")):
                found.setdefault(dependency, location)
    return found


def scan(dependency: Dependency) -> dict:
    """Return GuardDog's JSON assessment of a dependency version.

    GuardDog reports download and rule failures in the assessment's `errors`
    rather than through its exit status. Other per-package failures are
    returned the same way, so that each one becomes an "incomplete" alert.
    """
    if dependency.version.startswith("https://"):
        target = [dependency.version]
    else:
        target = [dependency.name, "--version", dependency.version]
    command = ["guarddog", dependency.ecosystem, "scan", *target, "--output-format", "json"]
    try:
        process = subprocess.run(command, capture_output=True, text=True, check=False, timeout=900)
    except subprocess.TimeoutExpired:
        return {"errors": {"timeout": "GuardDog did not finish within 15 minutes"}}
    try:
        report = json.loads(process.stdout)
    except json.JSONDecodeError:
        report = None
    if process.returncode != 0 or not isinstance(report, dict):
        return {"errors": {"guarddog": f"exit status {process.returncode}: {process.stderr}"}}
    label = (report.get("risk_score") or {}).get("label")
    if not report.get("errors") and label not in (RULES.keys() - {INCOMPLETE}) | {NO_RISK}:
        report["errors"] = {"risk_score": f"unrecognized risk label {label!r}"}
    return report


def rule_for(report: dict) -> str:
    """Return the SARIF rule ID for an assessment, or NO_RISK if it needs no alert."""
    if report.get("errors"):
        return INCOMPLETE
    return report["risk_score"]["label"]


def describe(dependency: Dependency, report: dict) -> str:
    """Summarize an assessment and its evidence as a plain-text alert message."""
    what = f"{dependency.ecosystem} dependency {dependency.name} {dependency.version}"
    risk_score = report.get("risk_score")
    if errors := report.get("errors"):
        lines = [f"GuardDog could not fully assess {what}:"]
        for key, message in errors.items():
            message = str(message).strip()
            if len(message) > MAX_ERROR_LENGTH:
                message = "..." + message[-MAX_ERROR_LENGTH:]
            lines.append(f"- {key}: {message}")
        if risk_score:
            lines.append(
                f"Its partial assessment is {risk_score['label']} "
                f"(risk score {risk_score['score']}/10)."
            )
    else:
        lines = [
            f"GuardDog rates {what} as {risk_score['label']} (risk score {risk_score['score']}/10)."
        ]
    if dependency.version.startswith("https://"):
        lines.append("GuardDog assessed the archive's source code only: no registry metadata.")
    risks = report.get("risks", [])
    if risks:
        lines.append("")
    for risk in risks[:MAX_RISKS_SHOWN]:
        rules = ", ".join(filter(None, [risk.get("threat_rule"), risk.get("capability_rule")]))
        where = f" at {risk['threat_location']}" if risk.get("threat_location") else ""
        lines.append(
            f"- {risk.get('severity')} {risk.get('name')}{where}: "
            f"{risk.get('threat_description')} ({rules})"
        )
    if len(risks) > MAX_RISKS_SHOWN:
        lines.append(f"- and {len(risks) - MAX_RISKS_SHOWN} more; see the alert's SARIF properties")
    return "\n".join(lines)


def to_sarif(assessments: list[tuple[Dependency, Location, dict]]) -> dict:
    rules = [
        {
            "id": rule,
            "shortDescription": {"text": description},
            "help": {"text": HELP, "markdown": HELP},
            "defaultConfiguration": {"level": level},
            "properties": {"security-severity": severity, "tags": ["security"]},
        }
        for rule, (level, severity, description) in RULES.items()
    ]
    results = [
        {
            "ruleId": rule_for(report),
            "message": {"text": describe(dependency, report)},
            "locations": [
                {
                    "physicalLocation": {
                        "artifactLocation": {"uri": location.path},
                        "region": {"startLine": location.line},
                    }
                }
            ],
            # GitHub identifies an alert by its rule, file and this hash alone.
            # Left unset, upload-sarif would hash the anchored line and the text
            # after it, so an unrelated edit nearby would reopen a dismissed
            # alert. Hashing the dependency version makes a dismissal cover
            # exactly that version, wherever its line moves.
            "partialFingerprints": {
                "primaryLocationLineHash": hashlib.sha256(str(dependency).encode()).hexdigest()
            },
            "properties": {
                "guarddog": {
                    key: report[key] for key in ("risk_score", "risks", "errors") if report.get(key)
                }
            },
        }
        for dependency, location, report in sorted(assessments, key=lambda a: a[1])
        if rule_for(report) != NO_RISK
    ]
    return {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "version": "2.1.0",
        "runs": [
            {
                "tool": {
                    "driver": {
                        "name": "GuardDog",
                        "informationUri": "https://github.com/DataDog/guarddog",
                        "rules": rules,
                    }
                },
                "results": results,
            }
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("output", type=Path, help="SARIF file to write")
    parser.add_argument("--jobs", type=int, default=16, help="parallel GuardDog scans")
    args = parser.parse_args()

    listing = subprocess.run(["git", "ls-files", "-z"], capture_output=True, text=True, check=True)
    dependencies = inventory(Path(), listing.stdout.split("\0"))
    print(f"Scanning {len(dependencies)} dependency versions with GuardDog")
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        reports = dict(zip(dependencies, pool.map(scan, dependencies), strict=True))
        # GuardDog's metadata rules make network lookups that occasionally time
        # out, so a failed scan gets one retry before it becomes an alert.
        retry = [d for d, report in reports.items() if report.get("errors")]
        reports.update(zip(retry, pool.map(scan, retry), strict=True))

    incomplete = {d: r["errors"] for d, r in reports.items() if r.get("errors")}
    for dependency, errors in incomplete.items():
        print(
            f"GuardDog could not fully assess {dependency}: {json.dumps(errors)}", file=sys.stderr
        )
    if len(incomplete) == len(reports):
        # A systemic failure, such as a broken GuardDog release or no network,
        # must fail the job rather than turn every dependency into an alert.
        # Workflow commands (::error::) are only parsed from stdout.
        print("::error::GuardDog could not assess any dependency; not writing SARIF.")
        return 1

    sarif = to_sarif([(d, dependencies[d], report) for d, report in reports.items()])
    for result in sarif["runs"][0]["results"]:
        location = result["locations"][0]["physicalLocation"]
        print(
            f"{result['ruleId']}: {result['message']['text'].splitlines()[0]} "
            f"({location['artifactLocation']['uri']}:{location['region']['startLine']})"
        )
    args.output.write_text(json.dumps(sarif, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {len(sarif['runs'][0]['results'])} results to {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
