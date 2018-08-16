import requests
import furl
import securedrop_proxy.util as util
import tempfile
import json

class Req:

    def __init__(self):
        self.method = ''
        self.path_query = ''
        self.body = None
        self.headers = None

class Response:

    def __init__(self, status):
        self.status = status
        self.body = None
        self.headers = None
        self.version = "0.1.1"

class Proxy:

    @staticmethod
    def _on_done(res):
        print(json.dumps(res.__dict__))

    def __init__(self, conf=None, req=Req(), on_save=None, on_done=None):
        self.conf = conf
        self.req = req
        self.res = None
        self.on_save = on_save
        if on_done is not None:
            self.on_done = on_done
        else:
            self.on_done = self._on_done

        self._prepared_request = None

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
            self.simple_error(400, 'Path provided in request did not look valid')
            raise ValueError('Path provided was invalid')

        try:
            url = furl.furl("{}://{}:{}/{}".format(scheme, host, port, path))
        except Exception as e:

            self.simple_error(500, 'Proxy error while generating URL to request')
            raise ValueError('Error generating URL from provided values')

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

        fh = tempfile.NamedTemporaryFile()

        for c in self._presp.iter_content(10):
            fh.write(c)

        res.headers = self._presp.headers

        self.on_save(fh, res)

        self.res = res

    def handle_response(self):

        ctype = util.parse_options_header(self._presp.headers['content-type'])

        if ctype[0] == "application/json":
            self.handle_json_response()
        else:
            self.handle_non_json_response()

        # headers is a Requests class which doesn't JSON serialize.
        # coerce it into a normal dict so it will
        self.res.headers = self.res.headers.__dict__

    def proxy(self):

        try:
            if self.on_save is None:
                self.simple_error(400, 'Request callback is not set.')
                raise ValueError('Request callback is not set.')

            self.prep_request()
            s = requests.Session()
            self._presp = s.send(self._prepared_request)
            self.handle_response()

        except ValueError:

            # effectively a 4xx error
            # we have set self.response to indicate an error
            pass

        # catch server errors here, handle maybe-differently from
        # ValueErrors...

        self.on_done(self.res)
