import http
import json
import sys
import tempfile
import types
import unittest
import uuid
from io import StringIO
from unittest.mock import patch

import requests
import vcr

from securedrop_proxy import proxy, version


class TestProxyValidConfig(unittest.TestCase):
    def setUp(self):
        self.conf_path = "tests/files/valid-config.yaml"

    def on_save(self, fh, res):
        res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
        res.headers["Content-Type"] = "application/json"
        res.body = json.dumps({"filename": self.fn})

    def on_done(self, res):
        res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
        res.headers["Content-Type"] = "application/json"

    def test_version(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = ""
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path)
        p.proxy()

        self.assertEqual(p.res.version, version.version)

    @vcr.use_cassette("fixtures/basic_proxy_functionality.yaml")
    def test_proxy_basic_functionality(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = ""
        req.headers = {"Accept": "application/json"}

        def on_save(self, fh, res):
            res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
            res.headers["Content-Type"] = "application/json"
            res.body = json.dumps({"filename": self.fn})

        p = proxy.Proxy(self.conf_path, req)
        # Patching on_save for test
        p.on_save = types.MethodType(on_save, p)
        p.fn = str(uuid.uuid4())
        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertEqual(p.res.body, json.dumps({"filename": p.fn}))
        self.assertEqual(p.res.headers["Content-Type"], "application/json")

    @vcr.use_cassette("fixtures/proxy_404.yaml")
    def test_proxy_produces_404(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = "/notfound"
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path, req)

        p.proxy()

        self.assertEqual(p.res.status, 404)
        self.assertEqual(p.res.headers["Content-Type"], "application/json")

    @vcr.use_cassette("fixtures/proxy_parameters.yaml")
    def test_proxy_handles_query_params_gracefully(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = "/posts?userId=1"
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path, req)

        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        for item in body:
            self.assertEqual(item["userId"], 1)

    # No cassette needed as no network request should be sent
    def test_proxy_400_bad_path(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = "http://badpath.lol/path"
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path, req)

        p.proxy()

        self.assertEqual(p.res.status, 400)
        self.assertEqual(p.res.headers["Content-Type"], "application/json")
        self.assertIn("Path provided in request did not look valid", p.res.body)

    @vcr.use_cassette("fixtures/proxy_200_valid_path.yaml")
    def test_proxy_200_valid_path(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = "/posts/1"
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path, req)

        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["userId"], 1)


class TestProxyInvalidConfig(unittest.TestCase):
    def setUp(self):
        self.conf_path = "tests/files/invalid-config.yaml"

    def on_save(self, fh, res):
        self.fn = str(uuid.uuid4())
        res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
        res.headers["Content-Type"] = "application/json"
        res.body = json.dumps({"filename": self.fn})

    # No cassette needed as no network request should be sent
    def test_proxy_500_misconfiguration(self):
        req = proxy.Req()
        req.method = "GET"
        req.path_query = "/posts/1"
        req.headers = {"Accept": "application/json"}

        p = proxy.Proxy(self.conf_path, req)

        p.proxy()

        self.assertEqual(p.res.status, 500)
        self.assertEqual(p.res.headers["Content-Type"], "application/json")
        self.assertIn("Proxy error while generating URL to request", p.res.body)


class TestServerErrorHandling(unittest.TestCase):
    def setUp(self):
        self.conf_path = "tests/files/local-config.yaml"

    def make_request(self, method="GET", path_query="/", headers=None):
        req = proxy.Req()
        req.method = method if method else "GET"
        req.path_query = path_query if path_query else "/"
        req.headers = headers if headers else {"Accept": "application/json"}
        return req

    def test_cannot_connect(self):
        """
        Test for "502 Bad Gateway" when the server can't be reached.
        """
        req = self.make_request()

        p = proxy.Proxy("tests/files/badgateway-config.yaml", req)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.BAD_GATEWAY)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "could not connect to server")

    def test_server_timeout(self):
        """
        Test for "504 Gateway Timeout" when the server times out.
        """

        class TimeoutProxy(proxy.Proxy):
            """
            Mocks a slow upstream server.

            VCR cassettes cannot represent a request that takes too
            long. This Proxy subclass raises the exception that would
            cause.
            """

            def prep_request(self):
                raise requests.exceptions.Timeout("test timeout")

        req = self.make_request(path_query="/tarpit")
        p = TimeoutProxy(self.conf_path, req, timeout=0.00001)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.GATEWAY_TIMEOUT)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "request timed out")

    @vcr.use_cassette("fixtures/proxy_bad_request.yaml")
    def test_bad_request(self):
        """
        Test handling of "400 Bad Request" from the server.
        """
        req = self.make_request(path_query="/bad")
        p = proxy.Proxy(self.conf_path, req)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.BAD_REQUEST)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], http.HTTPStatus.BAD_REQUEST.phrase.lower())

    @vcr.use_cassette("fixtures/proxy_unofficial_status.yaml")
    def test_unofficial_status(self):
        """
        Make sure we handle unofficial status codes from the server.

        Should the server ever need to return a status code not in
        Python's http.HTTPStatus, the proxy should still return a
        proper JSON error response with a generic error message.
        """
        req = self.make_request(path_query="/teapot")
        p = proxy.Proxy(self.conf_path, req)
        p.proxy()

        self.assertEqual(p.res.status, 499)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "unspecified server error")

    @vcr.use_cassette("fixtures/proxy_internal_server_error.yaml")
    def test_internal_server_error(self):
        """
        Test handling of "500 Internal Server Error" from the server.
        """
        req = self.make_request(path_query="/crash")
        p = proxy.Proxy(self.conf_path, req)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.INTERNAL_SERVER_ERROR)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], http.HTTPStatus.INTERNAL_SERVER_ERROR.phrase.lower())

    @vcr.use_cassette("fixtures/proxy_internal_error.yaml")
    def test_internal_error(self):
        """
        Ensure that the proxy returns JSON despite internal errors.
        """

        def bad_on_save(self, fh, res, conf):
            raise Exception("test internal proxy error")

        req = self.make_request()
        p = proxy.Proxy(self.conf_path, req)

        # Patching on_save for tests
        p.on_save = types.MethodType(bad_on_save, p)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.INTERNAL_SERVER_ERROR)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "internal proxy error")


class TestProxyMethods(unittest.TestCase):
    def setUp(self):
        self.res = proxy.Response(status=200)
        self.res.body = "babbys request"

        self.conf_path = "tests/files/dev-config.yaml"

    def test_err_on_done(self):
        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            with self.assertRaises(SystemExit):
                p = proxy.Proxy(self.conf_path)
                p.res = self.res
                p.err_on_done()
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response["status"], 200)
        self.assertEqual(response["body"], "babbys request")

    def test_on_done(self):
        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            p = proxy.Proxy(self.conf_path)
            p.res = self.res
            p.on_done()
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response["status"], 200)
        self.assertEqual(response["body"], "babbys request")

    def test_on_save_500_unhandled_error(self):
        fh = tempfile.NamedTemporaryFile()

        # Let's generate an error and ensure that an appropriate response
        # is sent back to the user
        with patch("subprocess.run", side_effect=IOError):
            p = proxy.Proxy(self.conf_path)
            p.on_save(fh, self.res)

        self.assertEqual(self.res.status, 500)
        self.assertEqual(self.res.headers["Content-Type"], "application/json")
        self.assertEqual(self.res.headers["X-Origin-Content-Type"], "application/json")
        self.assertIn("Unhandled error", self.res.body)

    def test_on_save_200_success(self):
        fh = tempfile.NamedTemporaryFile()

        p = proxy.Proxy(self.conf_path)
        p.on_save(fh, self.res)

        self.assertEqual(self.res.headers["Content-Type"], "application/json")
        self.assertEqual(self.res.headers["X-Origin-Content-Type"], "application/json")
        self.assertEqual(self.res.status, 200)
        self.assertIn("filename", self.res.body)

    @vcr.use_cassette("fixtures/proxy_callbacks.yaml")
    def test_custom_callbacks(self):
        """
        Test the handlers in a real proxy request.
        """
        conf = proxy.Conf()
        conf.host = "jsonplaceholder.typicode.com"
        conf.scheme = "https"
        conf.port = 443

        req = proxy.Req()
        req.method = "GET"

        on_save_addition = "added by the on_save callback\n"
        on_done_addition = "added by the on_done callback\n"

        def on_save(self, fh, res):
            res.headers["Content-Type"] = "text/plain"
            res.body = on_save_addition

        def on_done(self):
            self.res.headers["Content-Type"] = "text/plain"
            self.res.body += on_done_addition

        p = proxy.Proxy(self.conf_path, req)
        # Patching for tests
        p.conf = conf
        p.on_done = types.MethodType(on_done, p)
        p.on_save = types.MethodType(on_save, p)
        p.proxy()

        self.assertEqual(p.res.body, "{}{}".format(on_save_addition, on_done_addition))

    @vcr.use_cassette("fixtures/proxy_callbacks.yaml")
    def test_production_on_save(self):
        """
        Test on_save's production file handling.
        """
        conf = proxy.Conf()
        conf.host = "jsonplaceholder.typicode.com"
        conf.scheme = "https"
        conf.port = 443
        conf.dev = False
        conf.target_vm = "sd-viewer"

        with patch("subprocess.run") as patched_run:
            fh = tempfile.NamedTemporaryFile()
            p = proxy.Proxy(self.conf_path)
            # Patching for tests
            p.conf = conf
            p.on_save(fh, self.res)
            self.assertEqual(patched_run.call_args[0][0][0], "qvm-move-to-vm")


class TestConfig(unittest.TestCase):
    def setUp(self):
        self.conf_path = "tests/files/dev-config.yaml"

    def test_config_file_does_not_exist(self):
        def err_on_done(self):
            res = self.res.__dict__
            assert res["status"] == 500
            assert "Configuration file does not exist" in res["body"]
            assert res["headers"]["Content-Type"] == "application/json"
            sys.exit(1)

        p = proxy.Proxy(self.conf_path)
        p.err_on_done = types.MethodType(err_on_done, p)
        with self.assertRaises(SystemExit):
            p.read_conf("not/a/real/path")

    def test_config_file_when_yaml_is_invalid(self):
        def err_on_done(self):
            res = self.res.__dict__
            assert res["status"] == 500
            assert "YAML syntax error" in res["body"]
            assert res["headers"]["Content-Type"] == "application/json"
            sys.exit(1)

        p = proxy.Proxy(self.conf_path)
        p.err_on_done = types.MethodType(err_on_done, p)
        with self.assertRaises(SystemExit):
            p.read_conf("tests/files/invalid_yaml.yaml")

    def test_config_file_open_generic_exception(self):
        def err_on_done(self):
            res = self.res.__dict__
            assert res["status"] == 500
            assert res["headers"]["Content-Type"] == "application/json"
            sys.exit(1)

        p = proxy.Proxy(self.conf_path)
        p.err_on_done = types.MethodType(err_on_done, p)

        with self.assertRaises(SystemExit):
            # Patching open so that we can simulate a non-YAML error
            # (e.g. permissions)
            with patch("builtins.open", side_effect=IOError):
                p.read_conf("tests/files/valid-config.yaml")

    def test_config_has_valid_keys(self):
        p = proxy.Proxy("tests/files/valid-config.yaml")

        # Verify we have a valid Conf object
        self.assertEqual(p.conf.host, "jsonplaceholder.typicode.com")
        self.assertEqual(p.conf.port, 443)
        self.assertFalse(p.conf.dev)
        self.assertEqual(p.conf.scheme, "https")
        self.assertEqual(p.conf.target_vm, "compost")

    def test_config_500_when_missing_a_required_key(self):
        def err_on_done(self):
            res = self.res.__dict__
            assert res["status"] == 500
            assert "missing required keys" in res["body"]
            assert res["headers"]["Content-Type"] == "application/json"
            sys.exit(1)

        p = proxy.Proxy(self.conf_path)
        p.err_on_done = types.MethodType(err_on_done, p)

        with self.assertRaises(SystemExit):
            p.read_conf("tests/files/missing-key.yaml")

    def test_config_500_when_missing_target_vm(self):
        def err_on_done(self):
            res = self.res.__dict__
            assert res["status"] == 500
            assert "missing `target_vm` key" in res["body"]
            assert res["headers"]["Content-Type"] == "application/json"
            sys.exit(1)

        p = proxy.Proxy(self.conf_path)
        p.err_on_done = types.MethodType(err_on_done, p)

        with self.assertRaises(SystemExit):
            p.read_conf("tests/files/missing-target-vm.yaml")

    def test_dev_config(self):
        p = proxy.Proxy("tests/files/dev-config.yaml")
        assert p.conf.dev
