from io import StringIO
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

import vcr

from securedrop_proxy import callbacks
from securedrop_proxy import config
from securedrop_proxy import proxy


class TestCallbacks(unittest.TestCase):
    def setUp(self):
        self.res = proxy.Response(status=200)
        self.res.body = "babbys request"

        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https'
        self.conf.port = 443
        self.conf.dev = True

    def test_err_on_done(self):
        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            with self.assertRaises(SystemExit):
                callbacks.err_on_done(self.res)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response['status'], 200)
        self.assertEqual(response['body'], 'babbys request')

    def test_on_done(self):
        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            callbacks.on_done(self.res)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        self.assertEqual(response['status'], 200)
        self.assertEqual(response['body'], 'babbys request')

    def test_on_save_500_unhandled_error(self):
        fh = tempfile.NamedTemporaryFile()

        # Let's generate an error and ensure that an appropriate response
        # is sent back to the user
        with patch("subprocess.run", side_effect=IOError):
            callbacks.on_save(fh, self.res, self.conf)

        self.assertEqual(self.res.status, 500)
        self.assertEqual(self.res.headers['Content-Type'],
                         'application/json')
        self.assertEqual(self.res.headers['X-Origin-Content-Type'],
                         'application/json')
        self.assertIn('Unhandled error', self.res.body)

    def test_on_save_200_success(self):
        fh = tempfile.NamedTemporaryFile()

        callbacks.on_save(fh, self.res, self.conf)

        self.assertEqual(self.res.headers['Content-Type'],
                         'application/json')
        self.assertEqual(self.res.headers['X-Origin-Content-Type'],
                         'application/json')
        self.assertEqual(self.res.status, 200)
        self.assertIn('filename', self.res.body)

    @vcr.use_cassette("fixtures/proxy_callbacks.yaml")
    def test_custom_callbacks(self):
        """
        Test the handlers in a real proxy request.
        """
        conf = config.Conf()
        conf.host = 'jsonplaceholder.typicode.com'
        conf.scheme = 'https'
        conf.port = 443

        req = proxy.Req()
        req.method = "GET"

        on_save_addition = "added by the on_save callback\n"
        on_done_addition = "added by the on_done callback\n"

        def on_save(fh, res, conf):
            res.headers['Content-Type'] = 'text/plain'
            res.body = on_save_addition

        def on_done(res):
            res.headers['Content-Type'] = 'text/plain'
            res.body += on_done_addition

        p = proxy.Proxy(self.conf, req, on_save=on_save, on_done=on_done)
        p.proxy()

        self.assertEqual(
            p.res.body,
            "{}{}".format(on_save_addition, on_done_addition)
        )

    @vcr.use_cassette("fixtures/proxy_callbacks.yaml")
    def test_production_on_save(self):
        """
        Test on_save's production file handling.
        """
        conf = config.Conf()
        conf.host = 'jsonplaceholder.typicode.com'
        conf.scheme = 'https'
        conf.port = 443
        conf.dev = False
        conf.target_vm = "sd-svs-dispvm"

        with patch("subprocess.run") as patched_run:
            fh = tempfile.NamedTemporaryFile()
            callbacks.on_save(fh, self.res, conf)
            self.assertEqual(patched_run.call_args[0][0][0], "qvm-move-to-vm")
