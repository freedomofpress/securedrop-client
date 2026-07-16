import json
import time

import pytest


def sent_request_id(response: dict) -> str | None:
    """Extract the X-Request-ID the proxy sent upstream from a
    header_echo_server response, tolerating header-name casing."""
    body = json.loads(response["body"])
    headers = {name.lower(): value for name, value in body["headers"].items()}
    return headers.get("x-request-id")


def test_json_response(proxy_request):
    """test a JSON response"""
    test_input = {
        "method": "GET",
        "path_query": "/json",
        "stream": False,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    assert response["headers"]["content-type"] == "application/json"


@pytest.mark.parametrize("status_code", [200, 404, 503])
def test_status_codes(proxy_request, status_code):
    """HTTP errors are passed through cleanly"""
    test_input = {
        "method": "GET",
        "path_query": f"/status/{status_code}",
        "stream": False,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == status_code


@pytest.mark.parametrize("status_code", range(301, 309))
def test_redirect(proxy_request, status_code):
    """Redirects are not followed: the status code, headers (including `Location`), and response
    are proxied unmodified."""
    test_input = {
        "method": "GET",
        "path_query": f"/redirect-to?url=https://example.org&status_code={status_code}",
        "stream": False,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == status_code
    assert response["headers"]["location"] == "https://example.org"


def test_query_parameters(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/get?foo=bar",
        "stream": False,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    body = json.loads(response["body"])
    assert body["args"] == {"foo": "bar"}


def test_timeout(proxy_request, httpbin):
    start = time.time()
    test_input = {"method": "GET", "path_query": "/delay/10", "stream": False, "timeout": 1}
    result = proxy_request(input=test_input)
    assert result.returncode == 1
    assert (
        result.stderr.decode().strip()
        == f'{{"error":"error sending request for url (http://127.0.0.1:{httpbin.port}/delay/10): '
        + 'operation timed out"}'
    )
    end = time.time()
    # timeout was 1s, so let's graciously say this test needs to complete in less than 3 seconds
    assert (end - start) < 3


def test_streaming(proxy_request):
    count = 20
    test_input = {
        "method": "GET",
        "path_query": f"/drip?duration=5&numbytes={count}&code=200&delay=0",
        "stream": True,
        "timeout": 20,  # sec
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    stderr = json.loads(result.stderr.decode())
    assert "headers" in stderr
    assert result.stdout.decode() == "*" * count


def test_non_json_response(proxy_request):
    test_input = {"method": "GET", "path_query": "/html", "stream": True}
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    stderr = json.loads(result.stderr.decode())
    assert "headers" in stderr
    assert result.stdout.decode().splitlines()[0] == "<!DOCTYPE html>"


def test_headers(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/headers",
        "stream": False,
        "headers": {"X-Test-Header": "th"},
    }

    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    body = json.loads(response["body"])
    assert body["headers"]["X-Test-Header"] == "th"


def test_request_id_forwarded(proxy_request, header_echo_server):
    """A well-formed X-Request-ID is forwarded to the server unmodified, and
    the server's echoed X-Request-ID is passed back in the response headers"""
    request_id = "req-72d64b57-4632-4d3e-96b0-24a0428f7ec1"
    test_input = {
        "method": "GET",
        "path_query": "/",
        "stream": False,
        "headers": {"X-Request-ID": request_id},
    }

    result = proxy_request(input=test_input, origin=header_echo_server)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    assert sent_request_id(response) == request_id
    assert response["headers"]["x-request-id"] == request_id


def test_request_id_not_added_when_missing(proxy_request, header_echo_server):
    """The proxy doesn't invent an X-Request-ID when the client doesn't send
    one: end-to-end correlation is only as good as what the client provides"""
    test_input = {
        "method": "GET",
        "path_query": "/",
        "stream": False,
    }

    result = proxy_request(input=test_input, origin=header_echo_server)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    assert sent_request_id(response) is None


@pytest.mark.parametrize(
    "invalid",
    [
        "not a request ID",
        "req-72D64B57-4632-4D3E-96B0-24A0428F7EC1",
        "req-injected message into the logs!",
    ],
)
def test_request_id_invalid_rejected(proxy_request, header_echo_server, invalid):
    """A malformed X-Request-ID fails the request (and is logged as a
    warning), so a broken or compromised client VM can't inject arbitrary
    strings into the proxy's or server's logs; nothing is sent upstream"""
    test_input = {
        "method": "GET",
        "path_query": "/",
        "stream": False,
        "headers": {"X-Request-ID": invalid},
    }

    result = proxy_request(input=test_input, origin=header_echo_server)
    assert result.returncode == 1
    # Nothing was proxied: the request is rejected before anything is sent
    assert result.stdout == b""
    error = json.loads(result.stderr.decode())
    assert error["error"].startswith("invalid X-Request-ID header: ")


def test_body(proxy_request):
    body_input = {"id": 42, "title": "test"}
    test_input = {
        "method": "POST",
        "path_query": "/post",
        "stream": False,
        "body": json.dumps(body_input),
    }

    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 200
    body = json.loads(response["body"])
    assert body["json"] == body_input
