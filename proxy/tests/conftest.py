"""Setup for tests of fundamental `securedrop-proxy` behavior not tied to the SecureDrop SDK."""

import json
import os
import subprocess

import pytest


@pytest.fixture(scope="session")
def proxy_bin() -> str:
    if "PROXY_BIN" in os.environ:
        # allow running tests against e.g. a packaged binary
        return os.environ["PROXY_BIN"]
    # default debug path, expects `cargo build` to already have been run
    metadata = subprocess.check_output(["cargo", "metadata"])
    return json.loads(metadata)["target_directory"] + "/debug/securedrop-proxy"


@pytest.fixture
def proxy_request(httpbin, proxy_bin):
    def proxy_(input: bytes | dict, origin: str | None = None) -> subprocess.CompletedProcess:
        if isinstance(input, dict):
            input = json.dumps(input).encode()
        if origin is None:
            origin = httpbin.url
        return subprocess.run(
            [proxy_bin],
            env={"SD_PROXY_ORIGIN": origin},
            input=input,
            capture_output=True,
            check=False,
        )

    return proxy_
