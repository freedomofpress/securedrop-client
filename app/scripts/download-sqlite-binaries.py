#!/usr/bin/env python3

import argparse
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path

PLATFORM_MAP = {"Linux": "linux", "Darwin": "darwin"}
ARCH_MAP = {"x86_64": "x64", "arm64": "arm64", "aarch64": "arm64"}


BASE_URL = "https://github.com/WiseLibs/better-sqlite3/releases/download"
CHECKSUMS_FILE = Path(__file__).parent / "sqlite-checksums.json"


def load_checksums() -> dict:
    """Load checksums from JSON file"""
    return json.loads(CHECKSUMS_FILE.read_text())


def get_node_abi() -> str:
    """Get the Node.js ABI version dynamically"""
    result = subprocess.run(
        ["node", "-e", "console.log(process.versions.modules)"],
        capture_output=True,
        text=True,
        check=True,
    )
    abi_version = result.stdout.strip()
    return f"v{abi_version}"


def get_electron_abi() -> str:
    """
    Get the Electron ABI version dynamically

    We don't use `electron --abi` because it links to a lot of system libraries that
    might be missing from containers.
    """
    script_dir = Path(__file__).parent.parent

    version_file = script_dir / "node_modules" / "electron" / "dist" / "version"
    node_abi_path = script_dir / "node_modules" / "node-abi"

    if not version_file.exists():
        raise RuntimeError("Electron version file not found")
    if not node_abi_path.exists():
        raise RuntimeError("node-abi module not found")

    electron_version = version_file.read_text().strip()

    # Shell out to nodejs to invoke the node-abi library
    result = subprocess.run(
        [
            "node",
            "-e",
            f"console.log(require('{node_abi_path}').getAbi('{electron_version}', 'electron'))",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    abi_version = result.stdout.strip()
    return f"v{abi_version}"


def get_package_version() -> str:
    lock = Path(__file__).parent.parent / "pnpm-lock.yaml"
    for line in lock.read_text().splitlines():
        match = re.match(r"better-sqlite3@(\d+\.\d+\.\d+):", line.strip())
        if match:
            return match.group(1)

    raise RuntimeError("Unable to determine better-sqlite3 version")


def get_platform_arch():
    """Get platform and architecture in better-sqlite3 format"""
    system = platform.system()
    machine = platform.machine()

    plat = PLATFORM_MAP.get(system)
    arch = ARCH_MAP.get(machine)

    if not plat or not arch:
        raise RuntimeError(f"Unsupported platform: {system}-{machine}")

    return plat, arch


def calculate_checksum(file_path) -> str:
    """Calculate SHA256 checksum of a file"""
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()


def build_download_url(runtime, args):
    """Build the download URL for a binary"""
    filename = (
        f"better-sqlite3-v{args['package_version']}-{runtime}-"
        + f"{args['abi']}-{args['plat']}-{args['arch']}.tar.gz"
    )
    return f"{BASE_URL}/v{args['package_version']}/{filename}"


def download_file(url, output_path):
    """Download a file from URL to output_path"""
    print(f"Downloading: {url}")

    if not url.startswith("https://"):
        raise RuntimeError("Only HTTPS URLs can be downloaded")
    with urllib.request.urlopen(url) as response:  # noqa: S310  # nosemgrep: python.lang.security.audit.dynamic-urllib-use-detected.dynamic-urllib-use-detected
        if response.status != 200:
            raise RuntimeError(f"HTTP {response.status}")

        with open(output_path, "wb") as f:
            shutil.copyfileobj(response, f)


def extract_tar_gz(tar_path, extract_to):
    """Extract a tar.gz file"""
    print(f"Extracting: {tar_path} to {extract_to}")

    extract_to.mkdir(parents=True, exist_ok=True)

    with tarfile.open(tar_path, "r:gz") as tar:
        # TODO: use filter="data" once we're Python 3.12+
        tar.extractall(extract_to)  # noqa: S202


def find_node_file(directory):
    """Find the .node file in the extracted directory"""
    for file in directory.glob("**/*.node"):
        return file

    raise RuntimeError("Could not find .node file in extracted archive")


def get_checksum_key(runtime, args) -> str:
    """Get the checksum key based on the download URL pattern"""
    # Use the tar.gz filename as the key (without .tar.gz extension)
    url = build_download_url(runtime, args)
    tar_filename = Path(url).name
    # Remove .tar.gz extension
    return tar_filename.replace(".tar.gz", ".node")


def verify_node_checksum(node_file_path, runtime, args) -> None:
    """Verify the checksum of a .node file"""
    checksum_key = get_checksum_key(runtime, args)
    checksums = load_checksums()

    try:
        expected_checksum = checksums[checksum_key]
    except KeyError:
        raise RuntimeError(
            f"No checksum found for {checksum_key}. Run with --update-checksums to add it."
        )

    actual_checksum = calculate_checksum(node_file_path)
    if actual_checksum != expected_checksum:
        raise RuntimeError(
            f"Checksum mismatch for {checksum_key}!\n"
            f"  Expected: {expected_checksum}\n"
            f"  Got:      {actual_checksum}"
        )
    print(f"✓ Checksum verified: {checksum_key}")


def download_and_extract_binary(runtime, base_path, args, verify_checksum=True):
    """Download and extract a binary for the given runtime"""
    url = build_download_url(runtime, args)
    filename = Path(url).name

    # Create target directory
    target_dir = base_path / f"Release-{runtime}"
    target_dir.mkdir(parents=True, exist_ok=True)

    final_path = target_dir / "better_sqlite3.node"

    # Check if file already exists
    if final_path.exists():
        print(f"Binary already exists: {final_path}")
        if verify_checksum:
            verify_node_checksum(final_path, runtime, args)
            print(f"✓ Existing {runtime} binary checksum verified")
            return final_path
        else:
            print(f"✓ Using existing {runtime} binary (checksum verification skipped)")
            return final_path

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        download_path = temp_path / filename

        download_file(url, download_path)

        # Extract to temporary location
        extract_temp = temp_path / f"extract-{runtime}"
        extract_tar_gz(download_path, extract_temp)

        # Find the .node file
        node_file = find_node_file(extract_temp)

        # Verify checksum of the .node file
        if verify_checksum:
            verify_node_checksum(node_file, runtime, args)

        # Copy to final location
        shutil.copy2(node_file, final_path)

    print(f"✓ Successfully downloaded {runtime} binary")
    print(f"  Binary ready at: {final_path}")
    return final_path


def update_checksums_file(checksums) -> None:
    """Update the checksums JSON file"""
    CHECKSUMS_FILE.write_text(json.dumps(checksums, indent=2, sort_keys=True) + "\n")

    print(f"✓ Updated checksums in {CHECKSUMS_FILE.name}")
    print()
    print("New checksums:")
    for filename, checksum in sorted(checksums.items()):
        print(f"  {filename}")
        print(f"    {checksum}")


def main():
    parser = argparse.ArgumentParser(
        description="Download better-sqlite3 binaries with checksum verification"
    )
    parser.add_argument(
        "--update-checksums",
        action="store_true",
        help="Download binaries, calculate checksums, and update checksums file",
    )
    args_parsed = parser.parse_args()

    print("Downloading better-sqlite3 binaries...")

    plat, arch = get_platform_arch()
    node_abi = get_node_abi()
    electron_abi = get_electron_abi()
    args = {
        "plat": plat,
        "arch": arch,
        "package_version": get_package_version(),
    }
    print(f"Platform: {args['plat']}-{args['arch']}")
    print(f"better-sqlite3 version: {args['package_version']}")
    print(f"Node.js ABI: {node_abi}, Electron ABI: {electron_abi}")
    print()

    # Set up paths
    script_dir = Path(__file__).parent.parent
    base_path = script_dir / "node_modules" / "better-sqlite3" / "build"

    if not (script_dir / "node_modules" / "better-sqlite3").exists():
        print("better-sqlite3 not found in node_modules")
        print("Please run: pnpm install")
        sys.exit(1)

    if args_parsed.update_checksums:
        print("UPDATE CHECKSUMS MODE")
        print("Downloading binaries to calculate checksums...")
        print()

        checksums = {}

        # Generate checksums for all supported platforms and architectures
        platforms_arches = [
            (plat, arch) for plat in PLATFORM_MAP.values() for arch in set(ARCH_MAP.values())
        ]

        for plat, arch in platforms_arches:
            platform_args = {
                "plat": plat,
                "arch": arch,
                "package_version": args["package_version"],
            }

            print(f"Processing {plat}-{arch}...")

            # Node.js binary
            node_args = dict(**platform_args, abi=node_abi)
            node_path = download_and_extract_binary(
                "node", base_path, node_args, verify_checksum=False
            )
            checksum_key = get_checksum_key("node", node_args)
            checksums[checksum_key] = calculate_checksum(node_path)
            print(f"✓ Calculated checksum for {checksum_key}")

            # Electron binary
            electron_args = dict(**platform_args, abi=electron_abi)
            electron_path = download_and_extract_binary(
                "electron", base_path, electron_args, verify_checksum=False
            )
            checksum_key = get_checksum_key("electron", electron_args)
            checksums[checksum_key] = calculate_checksum(electron_path)
            print(f"✓ Calculated checksum for {checksum_key}")

            print()

        update_checksums_file(checksums)
        print()
        print("Now downloading and verifying binaries for current platform...")
        print()

    results = {}

    # Download Node.js binary
    results["node"] = download_and_extract_binary(
        "node", base_path, dict(**args, abi=node_abi), verify_checksum=True
    )
    # Download Electron binary
    results["electron"] = download_and_extract_binary(
        "electron", base_path, dict(**args, abi=electron_abi), verify_checksum=True
    )

    print()
    print("Download complete!")
    print()
    print("Binary locations:")
    for runtime, path in results.items():
        print(f"  {runtime.title()}: {path}")


if __name__ == "__main__":
    main()
