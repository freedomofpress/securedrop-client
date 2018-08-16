from io import StringIO
import json
import sys
import unittest

from securedrop_proxy import proxy
from securedrop_proxy import config


class TestConfig(unittest.TestCase):
    def setUp(self):
        self.p = proxy.Proxy()

        def err_on_done(res):
            print(json.dumps(res.__dict__))
            sys.exit(1)

        self.p.on_done = err_on_done

    def test_config_file_does_not_exist(self):
        saved_stdout = sys.stdout
        try:
            out = StringIO()
            sys.stdout = out
            with self.assertRaises(SystemExit):
                config.read_conf('not/a/real/path', self.p)
            output = out.getvalue().strip()
        finally:
            sys.stdout = saved_stdout

        response = json.loads(output)
        assert response['status'] == 500
        assert "Configuration file does not exist" in response['body']
        assert response['headers']['Content-Type'] == 'application/json'
