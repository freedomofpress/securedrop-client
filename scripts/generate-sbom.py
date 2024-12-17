#!/usr/bin/env python3
"""
Generate updated SBOMs for some of our components

We use the CycloneDX tools, which need to be installed with poetry and cargo.

While this script can be run directly, you should use `make sbom` in the
repository root.
"""

import shutil
import subprocess
import sys
from pathlib import Path

# Follow this version of the CycloneDX spec
SPEC_VERSION = "1.5"

root = Path(__file__).parent.parent
sboms = root / "sbom"


def check_deps():
    errors = False
    if not shutil.which("cargo-cyclonedx"):
        print("Cannot find cargo-cyclonedx; install with `cargo install cargo-cyclonedx`")
        errors = True
    if not shutil.which("cyclonedx-py"):
        print("Cannot find cyclonedx-py; make sure you are running this with `poetry run`")
        errors = True

    if errors:
        sys.exit(1)


def python():
    for build_requirements in root.glob("*/build-requirements.txt"):
        component = build_requirements.parent.name
        output = subprocess.check_output(
            [
                "cyclonedx-py",
                "requirements",
                "--output-reproducible",
                "--schema-version",
                SPEC_VERSION,
                str(build_requirements),
            ],
            text=True,
        )
        (sboms / f"securedrop-{component}.cdx.json").write_text(output)
        print(f"Created SBOM for {component}")


def rust():
    # Generate SBOMs that include all features for the x86_64 Linux target
    subprocess.check_call(
        [
            "cargo",
            "cyclonedx",
            "--all-features",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--format",
            "json",
            "--spec-version",
            SPEC_VERSION,
        ]
    )
    # Now find all the SBOMs it created and move them to the sbom directory
    for sbom in root.glob("*/*.cdx.json"):
        if sbom.parent.name == "sbom":
            # Already in the directory
            continue
        shutil.move(sbom, sboms / sbom.name)
        print(f"Created SBOM for {sbom.parent.name}")


def main():
    check_deps()
    python()
    rust()


if __name__ == "__main__":
    main()
