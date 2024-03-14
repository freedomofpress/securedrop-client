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


@pytest.mark.parametrize("status_code", (200, 404, 503))
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
        == '{"error":"error sending request for url (http://127.0.0.1:%s/delay/10): ' % httpbin.port
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
    assert "headers" in stderr.keys()
    assert result.stdout.decode() == "*" * count


def test_non_json_response(proxy_request):
    test_input = {"method": "GET", "path_query": "/html", "stream": True}
    result = proxy_request(input=test_input)
    assert result.returncode == 0
    stderr = json.loads(result.stderr.decode())
    assert "headers" in stderr.keys()
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
