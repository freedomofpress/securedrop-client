import contextlib
import http
import io
import json
import os
import sys
import tempfile
import unittest.mock

import vcr
from securedrop_proxy import entrypoint


@contextlib.contextmanager
def sdhome(*args, **kwds):
    with tempfile.TemporaryDirectory() as tmphome:
        os.environ["SECUREDROP_HOME"] = tmphome
        try:
            yield tmphome
        finally:
            del os.environ["SECUREDROP_HOME"]


class TestEntrypoint(unittest.TestCase):
    """
    Test the entrypoint used in production.
    """

    def test_missing_config(self):
        config_path = "/tmp/nonexistent-config.yaml"
        self.assertFalse(os.path.exists(config_path))

        output = None
        with unittest.mock.patch(
            "sys.argv", new_callable=lambda: ["sd-proxy", config_path]
        ) as mock_argv, unittest.mock.patch("sys.stdout", new_callable=io.StringIO) as mock_stdout:
            with self.assertRaises(SystemExit), sdhome():
                entrypoint.start()
            output = mock_stdout.getvalue()

        response = json.loads(output)
        self.assertEqual(response["status"], http.HTTPStatus.INTERNAL_SERVER_ERROR)
        body = json.loads(response["body"])
        self.assertEqual(
            body["error"], "Configuration file does not exist at {}".format(config_path)
        )

    def test_unwritable_log_folder(self):
        """
        Tests a permission problem in `configure_logging`.
        """
        output = None
        with sdhome() as home:
            os.chmod(home, 0o0444)
            with unittest.mock.patch("sys.stdout", new_callable=io.StringIO) as mock_stdout:
                with self.assertRaises(SystemExit):
                    entrypoint.start()
                output = mock_stdout.getvalue()
            os.chmod(home, 0o0700)

        response = json.loads(output)
        self.assertEqual(response["status"], http.HTTPStatus.INTERNAL_SERVER_ERROR)
        body = json.loads(response["body"])
        self.assertIn("Permission denied: ", body["error"])

    def test_wrong_number_of_arguments(self):
        with sdhome() as home:
            with unittest.mock.patch(
                "sys.argv", new_callable=lambda: ["sd-proxy"]
            ) as mock_argv, unittest.mock.patch(
                "sys.stdout", new_callable=io.StringIO
            ) as mock_stdout:
                with self.assertRaises(SystemExit):
                    entrypoint.start()
                output = mock_stdout.getvalue()

        response = json.loads(output)
        self.assertEqual(response["status"], http.HTTPStatus.INTERNAL_SERVER_ERROR)
        body = json.loads(response["body"])
        self.assertEqual(
            body["error"], "sd-proxy script not called with path to configuration file"
        )

    def test_empty_input(self):
        config_path = "tests/files/valid-config.yaml"
        self.assertTrue(os.path.exists(config_path))

        with sdhome() as home:
            with unittest.mock.patch(
                "sys.stdin", new_callable=lambda: io.StringIO("")
            ) as mock_stdin, unittest.mock.patch(
                "sys.stdout", new_callable=io.StringIO
            ) as mock_stdout, unittest.mock.patch(
                "sys.argv", new_callable=lambda: ["sd-proxy", config_path]
            ) as mock_argv:
                entrypoint.start()
                output = mock_stdout.getvalue()

        response = json.loads(output)
        self.assertEqual(response["status"], http.HTTPStatus.BAD_REQUEST)
        body = json.loads(response["body"])
        self.assertEqual(
            body["error"], "Invalid JSON in request"
        )

    @vcr.use_cassette("fixtures/main_json_response.yaml")
    def test_json_response(self):
        config_path = "tests/files/valid-config.yaml"
        self.assertTrue(os.path.exists(config_path))

        test_input = {
            "method": "GET",
            "path_query": "/posts?userId=1",
        }

        output = None
        with sdhome() as home, unittest.mock.patch(
            "sys.stdin", new_callable=lambda: io.StringIO(json.dumps(test_input))
        ) as mock_stding, unittest.mock.patch(
            "sys.stdout", new_callable=io.StringIO
        ) as mock_stdout, unittest.mock.patch(
            "sys.argv", new_callable=lambda: ["sd-proxy", config_path]
        ) as mock_argv:
            entrypoint.start()
            output = mock_stdout.getvalue()

        response = json.loads(output)
        self.assertEqual(response["status"], http.HTTPStatus.OK)
