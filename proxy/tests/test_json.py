import unittest

from securedrop_proxy import json


class JsonTest(unittest.TestCase):
    def test_dumps(self):
        """Simple check since this is a passthrough to stdlib json"""
        self.assertEqual(
            json.dumps({"foo": "bar", "baz": ["one"]}), '{"foo": "bar", "baz": ["one"]}'
        )

    def test_loads(self):
        # Verify basic loading works
        self.assertEqual(
            json.loads('{"foo": "bar", "baz": ["one"]}'), {"foo": "bar", "baz": ["one"]}
        )
        # But duplicate keys are rejected
        with self.assertRaises(ValueError) as exc:
            json.loads('{"foo": "bar", "foo": "baz"}')
        self.assertEqual(str(exc.exception), "Key 'foo' found twice in JSON object")
