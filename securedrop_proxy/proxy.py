import furl
import http
import json
import logging
import requests
import tempfile
import werkzeug

import securedrop_proxy.version as version
from securedrop_proxy import callbacks


logger = logging.getLogger(__name__)


class Req:
    def __init__(self):
        self.method = ""
        self.path_query = ""
        self.body = None
        self.headers = {}


class Response:
    def __init__(self, status):
        self.status = status
        self.body = None
        self.headers = {}
        self.version = version.version


class Proxy:
    def __init__(self, conf=None, req=Req(), on_save=None, on_done=None, timeout: float = None):
        self.conf = conf
        self.req = req
        self.res = None
        self.on_save = on_save
        if on_done is not None:
            self.on_done = on_done

        self.timeout = float(timeout) if timeout else 10

        self._prepared_request = None

    def on_done(self, res):
        callbacks.on_done(res)

    @staticmethod
    def valid_path(path):
        u = furl.furl(path)

        if u.host is not None:
            return False
        return True

    def simple_error(self, status, err):
        res = Response(status)
        res.body = json.dumps({"error": err})
        res.headers = {"Content-Type": "application/json"}

        self.res = res

    def prep_request(self):

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
        preq.stream = True
        preq.headers = self.req.headers
        preq.data = self.req.body
        prep = preq.prepare()

        self._prepared_request = prep

    def handle_json_response(self):

        res = Response(self._presp.status_code)

        res.headers = self._presp.headers
        res.body = self._presp.content.decode()

        self.res = res

    def handle_non_json_response(self):

        res = Response(self._presp.status_code)

        # Create a NamedTemporaryFile, we don't want
        # to delete it after closing.
        fh = tempfile.NamedTemporaryFile(delete=False)

        for c in self._presp.iter_content(10):
            fh.write(c)

        fh.close()

        res.headers = self._presp.headers

        self.on_save(fh, res, self.conf)

        self.res = res

    def handle_response(self):
        logger.debug("Handling response")

        ctype = werkzeug.http.parse_options_header(self._presp.headers["content-type"])

        if ctype[0] == "application/json":
            self.handle_json_response()
        else:
            self.handle_non_json_response()

        # headers is a Requests class which doesn't JSON serialize.
        # coerce it into a normal dict so it will
        self.res.headers = dict(self.res.headers)

    def proxy(self):

        try:
            if self.on_save is None:
                self.simple_error(
                    http.HTTPStatus.BAD_REQUEST, "Request on_save callback is not set."
                )
                raise ValueError("Request on_save callback is not set.")

            self.prep_request()
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
                    http.HTTPStatus(e.response.status_code).phrase.lower()
                )
            except ValueError:
                # Return a generic error message when the response
                # status code is not found in http.HTTPStatus.
                self.simple_error(e.response.status_code, "unspecified server error")
        except Exception as e:
            logger.error(e)
            self.simple_error(http.HTTPStatus.INTERNAL_SERVER_ERROR, "internal proxy error")
        self.on_done(self.res)
