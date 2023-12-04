import os
import subprocess


def test_missing_config(proxy_bin):
    env = os.environ.copy()
    if "SD_PROXY_ORIGIN" in env:
        del env["SD_PROXY_ORIGIN"]
    result = subprocess.run([proxy_bin], env=env, capture_output=True)
    assert result.returncode == 1
    assert result.stderr.decode().strip() == '{"error":"environment variable not found"}'


def test_empty_input(proxy_request):
    result = proxy_request(input=b"")
    assert result.returncode == 1
    assert (
        result.stderr.decode().strip() == '{"error":"EOF while parsing a value at line 1 column 0"}'
    )


def test_input_invalid(proxy_request):
    test_input = b'"foo": "bar", "baz": "bliff"}'
    result = proxy_request(input=test_input)
    assert result.returncode == 1
    assert (
        result.stderr.decode().strip()
        == '{"error":"invalid type: string \\"foo\\", '
        + 'expected struct IncomingRequest at line 1 column 5"}'
    )


def test_input_missing_keys(proxy_request):
    test_input = b'{"foo": "bar", "baz": "bliff"}'
    result = proxy_request(input=test_input)
    assert result.returncode == 1
    assert (
        result.stderr.decode().strip()
        == '{"error":"unknown field `foo`, expected one of `method`, '
        + '`path_query`, `stream`, `headers`, `body`, `timeout` at line 1 column 6"}'
    )


def test_invalid_origin(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/status/200",
        "stream": False,
    }
    # invalid port
    result = proxy_request(input=test_input, origin="http://127.0.0.1:-1/foo")
    assert result.returncode == 1
    assert result.stderr.decode().strip() == '{"error":"invalid port number"}'


def test_cannot_connect(proxy_request):
    test_input = {
        "method": "GET",
        "path_query": "/",
        "stream": False,
    }
    # .test is a reserved TLD, so it should never resolve
    result = proxy_request(input=test_input, origin="http://missing.test/foo")
    assert result.returncode == 1
    assert (
        result.stderr.decode().strip()
        == '{"error":"error sending request for url (http://missing.test/): '
        + "error trying to connect: dns error: failed to lookup address information: "
        + 'Name or service not known"}'
    )
