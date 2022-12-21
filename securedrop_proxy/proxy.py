import http
import logging
import os
import subprocess
import sys
import tempfile
import uuid
from typing import IO, Dict, Optional

import furl  # type: ignore
import requests
import werkzeug
import yaml

import securedrop_proxy.version as version
from securedrop_proxy import json

logger = logging.getLogger(__name__)


class Conf:
    scheme = ""
    host = ""
    port = 0
    dev = False
    target_vm = ""


class Req:
    def __init__(self) -> None:
        self.method = ""
        self.path_query = ""
        self.body = ""
        self.headers: Dict[str, str] = {}


class Response:
    def __init__(self, status: int) -> None:
        self.status = status
        self.body = ""
        self.headers: Dict[str, str] = {}
        self.version = version.version


class Proxy:
    def __init__(self, conf_path: str, req: Req = Req(), timeout: float = 10.0) -> None:
        self.read_conf(conf_path)

        self.req = req
        self.res: Optional[Response] = None
        self.timeout = float(timeout)

        self._prepared_request: Optional[requests.PreparedRequest] = None

    def on_done(self) -> None:
        print(json.dumps(self.res.__dict__))

    @staticmethod
    def valid_path(path: str) -> bool:
        u = furl.furl(path)

        if u.host is not None:
            return False
        return True

    def err_on_done(self):
        print(json.dumps(self.res.__dict__))
        sys.exit(1)

    def read_conf(self, conf_path: str) -> None:

        if not os.path.isfile(conf_path):
            self.simple_error(500, "Configuration file does not exist at {}".format(conf_path))
            self.err_on_done()

        try:
            with open(conf_path) as fh:
                conf_in = yaml.safe_load(fh)
        except yaml.YAMLError:
            self.simple_error(
                500,
                "YAML syntax error while reading configuration file {}".format(conf_path),
            )
            self.err_on_done()
        except Exception:
            self.simple_error(
                500,
                "Error while opening or reading configuration file {}".format(conf_path),
            )
            self.err_on_done()

        req_conf_keys = set(("host", "scheme", "port"))
        missing_keys = req_conf_keys - set(conf_in.keys())
        if len(missing_keys) > 0:
            self.simple_error(
                500, "Configuration file missing required keys: {}".format(missing_keys)
            )
            self.err_on_done()

        self.conf = Conf()
        self.conf.host = conf_in["host"]
        self.conf.scheme = conf_in["scheme"]
        self.conf.port = conf_in["port"]

        if "dev" in conf_in and conf_in["dev"]:
            self.conf.dev = True
        else:
            if "target_vm" not in conf_in:
                self.simple_error(
                    500,
                    (
                        "Configuration file missing `target_vm` key, which is required "
                        "when not in development mode"
                    ),
                )
                self.err_on_done()

            self.conf.target_vm = conf_in["target_vm"]

    # callback for handling non-JSON content. in production-like
    # environments, we want to call `qvm-move-to-vm` (and expressly not
    # `qvm-move`, since we want to include the destination VM name) to
    # move the content to the target VM. for development and testing, we
    # keep the file on the local VM.
    #
    # In any case, this callback mutates the given result object (in
    # `res`) to include the name of the new file, or to indicate errors.
    def on_save(self, fh: IO[bytes], res: Response) -> None:
        fn = str(uuid.uuid4())

        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                tmpfile = os.path.join(os.path.abspath(tmpdir), fn)
                subprocess.run(["cp", fh.name, tmpfile])
                if self.conf.dev is not True:
                    subprocess.run(["qvm-move-to-vm", self.conf.target_vm, tmpfile])
        except Exception:
            res.status = 500
            res.headers["Content-Type"] = "application/json"
            res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
            res.body = json.dumps(
                {"error": "Unhandled error while handling non-JSON content, sorry"}
            )
            return

        res.headers["Content-Type"] = "application/json"
        res.headers["X-Origin-Content-Type"] = res.headers["Content-Type"]
        res.body = json.dumps({"filename": fn})

    def simple_error(self, status: int, err: str) -> None:
        res = Response(status)
        res.body = json.dumps({"error": err})
        res.headers = {"Content-Type": "application/json"}

        self.res = res

    def prep_request(self) -> None:

        scheme = self.conf.scheme
        host = self.conf.host
        port = self.conf.port

        path = self.req.path_query
        method = self.req.method

        if not self.valid_path(path):
            self.simple_error(400, "Path provided in request did not look valid")
            raise ValueError("Path provided was invalid")

        try:
            url = furl.furl("{}://{}:{}/{}".format(scheme, host, port, path))
        except Exception as e:
            logger.error(e)
            self.simple_error(500, "Proxy error while generating URL to request")
            raise ValueError("Error generating URL from provided values")

        url.path.normalize()

        preq = requests.Request(method, url.url)
        preq.headers = self.req.headers
        preq.data = self.req.body
        prep = preq.prepare()

        self._prepared_request = prep

    def handle_json_response(self) -> None:

        res = Response(self._presp.status_code)

        res.headers = dict(self._presp.headers)
        res.body = self._presp.content.decode()

        self.res = res

    def handle_non_json_response(self) -> None:

        res = Response(self._presp.status_code)

        # Create a NamedTemporaryFile, we don't want
        # to delete it after closing.
        fh = tempfile.NamedTemporaryFile(delete=False)

        for c in self._presp.iter_content(10):
            fh.write(c)

        fh.close()

        res.headers = dict(self._presp.headers)

        self.on_save(fh, res)

        self.res = res

    def handle_response(self) -> None:
        logger.debug("Handling response")

        ctype = werkzeug.http.parse_options_header(self._presp.headers["content-type"])

        if ctype[0] == "application/json":
            self.handle_json_response()
        else:
            self.handle_non_json_response()

        # https://mypy.readthedocs.io/en/latest/kinds_of_types.html#union-types
        # To make sure that mypy knows the type of self.res is not None.
        assert self.res
        # headers is a Requests class which doesn't JSON serialize.
        # coerce it into a normal dict so it will
        self.res.headers = dict(self.res.headers)

    def proxy(self) -> None:

        try:

            self.prep_request()
            # To confirm that we have a prepared request before the proxy call
            assert self._prepared_request
            logger.debug("Sending request")
            s = requests.Session()
            self._presp = s.send(self._prepared_request, timeout=self.timeout)
            self._presp.raise_for_status()
            self.handle_response()
        except ValueError as e:
            logger.error(e)

            # effectively a 4xx error
            # we have set self.response to indicate an error
            pass
        except requests.exceptions.Timeout as e:
            # Timeout covers both ConnectTimeout and ReadTimeout
            logger.error(e)
            self.simple_error(http.HTTPStatus.GATEWAY_TIMEOUT, "request timed out")
        except (
            requests.exceptions.ConnectionError,  # covers ProxyError, SSLError
            requests.exceptions.TooManyRedirects,
        ) as e:
            logger.error(e)
            self.simple_error(http.HTTPStatus.BAD_GATEWAY, "could not connect to server")
        except requests.exceptions.HTTPError as e:
            logger.error(e)
            try:
                self.simple_error(
                    e.response.status_code,
                    http.HTTPStatus(e.response.status_code).phrase.lower(),
                )
            except ValueError:
                # Return a generic error message when the response
                # status code is not found in http.HTTPStatus.
                self.simple_error(e.response.status_code, "unspecified server error")
        except Exception as e:
            logger.error(e)
            self.simple_error(http.HTTPStatus.INTERNAL_SERVER_ERROR, "internal proxy error")
        self.on_done()
