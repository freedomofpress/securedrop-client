from io import StringIO
import json
import sys
import unittest
from unittest.mock import patch

from securedrop_proxy import proxy
from securedrop_proxy import config


class TestConfig(unittest.TestCase):
    def setUp(self):
        self.p = proxy.Proxy()

    def test_config_file_does_not_exist(self):
        def err_on_done(res):
            res = res.__dict__
            self.assertEquals(res['status'], 500)
            self.assertIn("Configuration file does not exist",
                          res['body'])
            self.assertEquals(res['headers']['Content-Type'],
                              'application/json')
            sys.exit(1)

        self.p.on_done = err_on_done
        with self.assertRaises(SystemExit):
            config.read_conf('not/a/real/path', self.p)

    def test_config_file_when_yaml_is_invalid(self):
        def err_on_done(res):
            res = res.__dict__
            self.assertEquals(res['status'], 500)
            self.assertIn("YAML syntax error", res['body'])
            self.assertEquals(res['headers']['Content-Type'],
                              'application/json')
            sys.exit(1)

        self.p.on_done = err_on_done
        with self.assertRaises(SystemExit):
            config.read_conf('tests/files/invalid_yaml.yaml', self.p)

    def test_config_file_open_generic_exception(self):
        def err_on_done(res):
            res = res.__dict__
            self.assertEquals(res['status'], 500)
            self.assertEquals(res['headers']['Content-Type'],
                              'application/json')
            sys.exit(1)

        self.p.on_done = err_on_done

        with self.assertRaises(SystemExit):
            # Patching open so that we can simulate a non-YAML error
            # (e.g. permissions)
            with patch("builtins.open", side_effect=IOError):
                config.read_conf('tests/files/valid-config.yaml', self.p)

    def test_config_has_valid_keys(self):
        c = config.read_conf('tests/files/valid-config.yaml', self.p)

        # Verify we have a valid Conf object
        self.assertEquals(c.host, 'jsonplaceholder.typicode.com')
        self.assertEquals(c.port, 443)
        self.assertFalse(c.dev)
        self.assertEquals(c.scheme, 'https')
        self.assertEquals(c.target_vm, 'compost')
