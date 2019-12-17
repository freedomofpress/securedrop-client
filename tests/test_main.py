import http
from io import StringIO
import json
import subprocess
import sys
import unittest
import uuid

import vcr

from securedrop_proxy import config
from securedrop_proxy import main
from securedrop_proxy import proxy


class TestMain(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https'
        self.conf.port = 443
        self.conf.dev = True

    @vcr.use_cassette('fixtures/main_json_response.yaml')
    def test_json_response(self):
        test_input_json = """{ "method": "GET",
                            "path_query": "/posts?userId=1" }"""

        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        # Use custom callbacks
        def on_save(res, fh, conf):
            pass

        def on_done(res):
            self.assertEqual(res.status, http.HTTPStatus.OK)
            print(json.dumps(res.__dict__))

        self.p = proxy.Proxy(self.conf, req, on_save, on_done)

        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            main.__main__(test_input_json, self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        for item in json.loads(response['body']):
            self.assertEqual(item['userId'], 1)

    @vcr.use_cassette('fixtures/main_non_json_response.yaml')
    def test_non_json_response(self):
        test_input_json = """{ "method": "GET",
                               "path_query": "" }"""

        def on_save(fh, res, conf):
            self.fn = str(uuid.uuid4())

            subprocess.run(["cp", fh.name, "/tmp/{}".format(self.fn)])

            res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
            res.headers['Content-Type'] = 'application/json'
            res.body = json.dumps({'filename': self.fn})

        self.p = proxy.Proxy(self.conf, proxy.Req(), on_save)

        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            main.__main__(test_input_json, self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response['status'], 200)

        # The proxy should have created a filename in the response body
        self.assertIn('filename', response['body'])

        # The file should not be empty
        with open("/tmp/{}".format(self.fn)) as f:
            saved_file = f.read()

        # We expect HTML content in the file from the test data
        self.assertIn("<!DOCTYPE html>", saved_file)

    def test_input_invalid_json(self):
        test_input_json = """"foo": "bar", "baz": "bliff" }"""

        def on_save(fh, res, conf):
            pass

        def on_done(res):
            res = res.__dict__
            self.assertEqual(res['status'], 400)
            sys.exit(1)

        p = proxy.Proxy(self.conf, proxy.Req(), on_save, on_done)

        with self.assertRaises(SystemExit):
            main.__main__(test_input_json, p)

    def test_input_missing_keys(self):
        test_input_json = """{ "foo": "bar", "baz": "bliff" }"""

        def on_save(fh, res, conf):
            pass

        def on_done(res):
            res = res.__dict__
            self.assertEqual(res['status'], 400)
            self.assertEqual(res['body'], '{"error": "Missing keys in request"}')
            sys.exit(1)

        p = proxy.Proxy(self.conf, proxy.Req(), on_save, on_done)
        with self.assertRaises(SystemExit):
            main.__main__(test_input_json, p)

    @vcr.use_cassette('fixtures/main_json_response.yaml')
    def test_input_headers(self):
        test_input = {
            "method": "GET",
            "path_query": "/posts?userId=1",
            "headers": { "X-Test-Header": "th" }
        }

        def on_save(fh, res, conf):
            pass

        p = proxy.Proxy(self.conf, proxy.Req(), on_save)
        main.__main__(json.dumps(test_input), p)
        self.assertEqual(p.req.headers, test_input["headers"])

    @vcr.use_cassette('fixtures/main_input_body.yaml')
    def test_input_body(self):
        test_input = {
            "method": "POST",
            "path_query": "/posts",
            "body": { "id": 42, "title": "test" }
        }

        def on_save(fh, res, conf):
            pass

        p = proxy.Proxy(self.conf, proxy.Req(), on_save)
        main.__main__(json.dumps(test_input), p)
        self.assertEqual(p.req.body, test_input["body"])

    @vcr.use_cassette('fixtures/main_non_json_response.yaml')
    def test_default_callbacks(self):
        test_input = {
            "method": "GET",
            "path_query": "",
        }

        p = proxy.Proxy(self.conf, proxy.Req())
        with unittest.mock.patch("securedrop_proxy.callbacks.on_done") as on_done, unittest.mock.patch("securedrop_proxy.callbacks.on_save") as on_save:
            main.__main__(json.dumps(test_input), p)
            self.assertEqual(on_save.call_count, 1)
            self.assertEqual(on_done.call_count, 1)
