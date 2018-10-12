from io import StringIO
import json
import subprocess
import sys
import unittest
import uuid

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
            res = res.__dict__
            self.assertEqual(res['status'], 200)

        self.p = proxy.Proxy(self.conf, req, on_save)
        self.p.on_done = on_done
        self.p.proxy()

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
        self.p.proxy()

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
        self.assertIn("<html>", saved_file)

    def test_error_response(self):
        test_input_json = """"foo": "bar", "baz": "bliff" }"""

        def on_save(fh, res, conf):
            pass

        def on_done(res):
            res = res.__dict__
            self.assertEqual(res['status'], 400)
            sys.exit(1)

        self.p = proxy.Proxy(self.conf, proxy.Req(), on_save)
        self.p.on_done = on_done

        with self.assertRaises(SystemExit):
            self.p.proxy()
            main.__main__(test_input_json, self.p)
