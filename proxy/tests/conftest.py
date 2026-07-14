"""Setup for tests of fundamental `securedrop-proxy` behavior not tied to the SecureDrop SDK."""

import json
import os
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

import pytest

# HACK Add the parent directory to the sys.path
# (bypass need for proper python project structure)
sys.path.append(str(Path(__file__).resolve().parent.parent))


@pytest.fixture(scope="session")
def proxy_bin() -> str:
    if "PROXY_BIN" in os.environ:
        # allow running tests against e.g. a packaged binary
        return os.environ["PROXY_BIN"]
    # default debug path, expects `cargo build` to already have been run
    metadata = subprocess.check_output(["cargo", "metadata"])
    return json.loads(metadata)["target_directory"] + "/debug/securedrop-proxy"


@pytest.fixture
def header_echo_server():
    """Origin that echoes the request headers into the response body (and the
    request's X-Request-ID into the response headers).  httpbin can't be used
    to observe forwarded request headers here because it hides X-Request-Id
    from /headers as an "environment header" (httpbin.helpers.ENV_HEADERS)."""

    class EchoHandler(BaseHTTPRequestHandler):
        def do_GET(self):
            body = json.dumps({"headers": dict(self.headers)}).encode()
            self.send_response(200)
            request_id = self.headers.get("X-Request-ID")
            if request_id:
                self.send_header("X-Request-ID", request_id)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *args):
            pass

    server = HTTPServer(("127.0.0.1", 0), EchoHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    yield f"http://127.0.0.1:{server.server_port}"
    server.shutdown()


@pytest.fixture
def proxy_request(httpbin, proxy_bin):
    def proxy_(
        input: bytes | dict, origin: str | None = None, use_tor=False
    ) -> subprocess.CompletedProcess:
        if isinstance(input, dict):
            input = json.dumps(input).encode()
        if origin is None:
            origin = httpbin.url

        env = {"SD_PROXY_ORIGIN": origin}
        if not use_tor:
            env["DISABLE_TOR"] = "yes"

        return subprocess.run(
            [proxy_bin],
            env=env,
            input=input,
            capture_output=True,
            check=False,
        )

    return proxy_
