import http
import json
import subprocess
import sys
import types
import unittest
import uuid
from io import StringIO

import vcr

from securedrop_proxy import main, proxy


class TestMain(unittest.TestCase):
    def setUp(self):
        self.conf_path = "tests/files/valid-config.yaml"

    @vcr.use_cassette("fixtures/main_json_response.yaml")
    def test_json_response(self):
        test_input_json = """{ "method": "GET",
                            "path_query": "/posts?userId=1" }"""

        req = proxy.Req()
        req.method = "GET"
        req.path_query = ""
        req.headers = {"Accept": "application/json"}

        # Use custom callbacks
        def on_save(self, fh, res):
            pass

        def on_done(self):
            assert self.res.status == http.HTTPStatus.OK
            print(json.dumps(self.res.__dict__))

        self.p = proxy.Proxy(self.conf_path, req)

        # Patching on_save and on_done

        self.p.on_done = types.MethodType(on_done, self.p)
        self.p.on_save = types.MethodType(on_save, self.p)

        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            main.__main__(test_input_json, self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        for item in json.loads(response["body"]):
            self.assertEqual(item["userId"], 1)

    @vcr.use_cassette("fixtures/main_json_response_with_timeout.yaml")
    def test_json_response_with_timeout(self):
        test_input_json = """{ "method": "GET",
                            "path_query": "/posts?userId=1",
                            "timeout": 40.0 }"""

        req = proxy.Req()
        req.method = "GET"
        req.path_query = ""
        req.headers = {"Accept": "application/json"}

        # Use custom callbacks
        def on_save(self, fh, res):
            pass

        def on_done(self):
            assert self.res.status == http.HTTPStatus.OK
            print(json.dumps(self.res.__dict__))

        self.p = proxy.Proxy(self.conf_path, req)

        # Patching on_save and on_done

        self.p.on_done = types.MethodType(on_done, self.p)
        self.p.on_save = types.MethodType(on_save, self.p)

        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            main.__main__(test_input_json, self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        # Test that the right timeout was set in proxy object
        assert self.p.timeout == 40.0

        response = json.loads(output)
        for item in json.loads(response["body"]):
            self.assertEqual(item["userId"], 1)

    @vcr.use_cassette("fixtures/main_non_json_response.yaml")
    def test_non_json_response(self):
        test_input_json = """{ "method": "GET",
                               "path_query": "" }"""

        def on_save(self, fh, res):
            subprocess.run(["cp", fh.name, "/tmp/{}".format(self.fn)])

            res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
            res.headers["Content-Type"] = "application/json"
            res.body = json.dumps({"filename": self.fn})

        self.p = proxy.Proxy(self.conf_path, proxy.Req())

        # Patching on_save to tests
        self.p.on_save = types.MethodType(on_save, self.p)
        self.p.fn = str(uuid.uuid4())

        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            main.__main__(test_input_json, self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response["status"], 200)

        # The proxy should have created a filename in the response body
        self.assertIn("filename", response["body"])

        # The file should not be empty
        with open("/tmp/{}".format(self.p.fn)) as f:
            saved_file = f.read()

        # We expect HTML content in the file from the test data
        self.assertIn("<!DOCTYPE html>", saved_file)

    def test_input_invalid_json(self):
        test_input_json = """"foo": "bar", "baz": "bliff" }"""

        def on_save(self, fh, res):
            pass

        def on_done(self):
            res = self.res.__dict__
            assert res["status"] == 400
            sys.exit(1)

        p = proxy.Proxy(self.conf_path, proxy.Req())

        # patching on_save and on_done for tests

        p.on_done = types.MethodType(on_done, p)
        p.on_save = types.MethodType(on_save, p)

        with self.assertRaises(SystemExit):
            main.__main__(test_input_json, p)

    def test_input_missing_keys(self):
        test_input_json = """{ "foo": "bar", "baz": "bliff" }"""

        def on_save(self, fh, res):
            pass

        def on_done(self):
            res = self.res.__dict__
            assert res["status"] == 400
            assert res["body"] == '{"error": "Missing keys in request"}', res
            sys.exit(1)

        p = proxy.Proxy(self.conf_path, proxy.Req())

        # patching on_save and on_done for tests

        p.on_done = types.MethodType(on_done, p)
        p.on_save = types.MethodType(on_save, p)

        with self.assertRaises(SystemExit):
            main.__main__(test_input_json, p)

    @vcr.use_cassette("fixtures/main_input_headers.yaml")
    def test_input_headers(self):
        test_input = {
            "method": "GET",
            "path_query": "/posts?userId=1",
            "headers": {"X-Test-Header": "th"},
        }

        def on_save(self, fh, res):
            pass

        p = proxy.Proxy(self.conf_path, proxy.Req())
        main.__main__(json.dumps(test_input), p)
        self.assertEqual(p.req.headers, test_input["headers"])

    @vcr.use_cassette("fixtures/main_input_body.yaml")
    def test_input_body(self):
        test_input = {
            "method": "POST",
            "path_query": "/posts",
            "body": {"id": 42, "title": "test"},
        }

        def on_save(self, fh, res):
            pass

        p = proxy.Proxy(self.conf_path, proxy.Req())

        # Patching on_save for tests

        p.on_save = types.MethodType(on_save, p)

        main.__main__(json.dumps(test_input), p)
        self.assertEqual(p.req.body, test_input["body"])

    @vcr.use_cassette("fixtures/main_non_json_response.yaml")
    def test_default_callbacks(self):
        test_input = {
            "method": "GET",
            "path_query": "",
        }

        p = proxy.Proxy(self.conf_path, proxy.Req())
        p.on_done = unittest.mock.MagicMock()
        p.on_save = unittest.mock.MagicMock()

        main.__main__(json.dumps(test_input), p)
        self.assertEqual(p.on_save.call_count, 1)
        self.assertEqual(p.on_done.call_count, 1)
