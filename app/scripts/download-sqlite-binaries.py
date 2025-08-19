#!/usr/bin/env python3

import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path

PLATFORM_MAP = {"Linux": "linux", "Darwin": "darwin", "Windows": "win32"}
ARCH_MAP = {"x86_64": "x64", "arm64": "arm64", "aarch64": "arm64"}


BASE_URL = "https://github.com/WiseLibs/better-sqlite3/releases/download"

# TODO: implement checksum verification if we use these in production


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

    with urllib.request.urlopen(url) as response:  # noqa: S310
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


def download_and_extract_binary(runtime, base_path, args):
    """Download and extract a binary for the given runtime"""
    url = build_download_url(runtime, args)
    filename = Path(url).name

    # Create target directory
    target_dir = base_path / f"Release-{runtime}"
    target_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        download_path = temp_path / filename

        download_file(url, download_path)

        # Extract to temporary location
        extract_temp = temp_path / f"extract-{runtime}"
        extract_tar_gz(download_path, extract_temp)

        # Find the .node file
        node_file = find_node_file(extract_temp)

        # Copy to final location
        final_path = target_dir / "better_sqlite3.node"
        shutil.copy2(node_file, final_path)

    print(f"✓ Successfully downloaded {runtime} binary")
    print(f"  Binary ready at: {final_path}")
    return final_path


def main():
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

    results = {}

    # Download Node.js binary
    results["node"] = download_and_extract_binary("node", base_path, dict(**args, abi=node_abi))
    # Download Electron binary
    results["electron"] = download_and_extract_binary(
        "electron", base_path, dict(**args, abi=electron_abi)
    )

    print()
    print("Download complete!")
    print()
    print("Binary locations:")
    for runtime, path in results.items():
        print(f"  {runtime.title()}: {path}")


if __name__ == "__main__":
    main()
