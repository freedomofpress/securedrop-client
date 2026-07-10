import json
import time

import pytest


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
    assert stderr["status"] == 200
    assert "headers" in stderr
    assert result.stdout.decode() == "*" * count


@pytest.mark.parametrize("status_code", [401, 403, 404, 500])
def test_stream_status_codes(proxy_request, status_code):
    """Stream errors retain the legacy JSON envelope for compatibility."""
    test_input = {
        "method": "GET",
        "path_query": f"/status/{status_code}",
        "stream": True,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == status_code
    assert "headers" in response
    assert result.stderr == b""


def test_large_stream_error_body_is_truncated(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/drip?duration=0&numbytes=70000&code=500&delay=0",
        "stream": True,
        "timeout": 20,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 500
    assert "[response body truncated at 65536 bytes]" in response["body"]
    assert result.stderr == b""


def test_stream_error_body_is_preserved_within_limit(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/drip?duration=0&numbytes=16&code=401&delay=0",
        "stream": True,
        "timeout": 20,
    }
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    response = json.loads(result.stdout.decode())
    assert response["status"] == 401
    assert response["body"] == "*" * 16
    assert result.stderr == b""


def test_non_json_response(proxy_request):
    test_input = {"method": "GET", "path_query": "/html", "stream": True}
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    stderr = json.loads(result.stderr.decode())
    assert stderr["status"] == 200
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
