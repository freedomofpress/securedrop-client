import http
import json
import unittest
import uuid

import requests
import vcr

from securedrop_proxy import callbacks
from securedrop_proxy import proxy
from securedrop_proxy import config
from securedrop_proxy import version


class TestProxyValidConfig(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https'
        self.conf.port = 443

    def on_save(self, fh, res, conf):
        self.fn = str(uuid.uuid4())
        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.headers['Content-Type'] = 'application/json'
        res.body = json.dumps({'filename': self.fn})

    def on_done(self, res):
        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.headers['Content-Type'] = 'application/json'

    def test_version(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy()
        p.proxy()

        self.assertEqual(p.res.version, version.version)

    def test_400_if_callback_not_set(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy()
        p.proxy()

        self.assertEqual(p.res.status, 400)

    @vcr.use_cassette('fixtures/basic_proxy_functionality.yaml')
    def test_proxy_basic_functionality(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertEqual(p.res.body, json.dumps({'filename': self.fn}))
        self.assertEqual(p.res.headers['Content-Type'], 'application/json')

    @vcr.use_cassette('fixtures/proxy_404.yaml')
    def test_proxy_produces_404(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = '/notfound'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req)
        p.on_save = self.on_save
        p.on_done = self.on_done
        p.proxy()

        self.assertEqual(p.res.status, 404)
        self.assertEqual(p.res.headers['Content-Type'], 'application/json')

    @vcr.use_cassette('fixtures/proxy_parameters.yaml')
    def test_proxy_handles_query_params_gracefully(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = '/posts?userId=1'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertIn('application/json', p.res.headers['Content-Type'])
        body = json.loads(p.res.body)
        for item in body:
            self.assertEqual(item['userId'], 1)

    # No cassette needed as no network request should be sent
    def test_proxy_400_bad_path(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = 'http://badpath.lol/path'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req)
        p.on_save = self.on_save
        p.on_done = self.on_done
        p.proxy()

        self.assertEqual(p.res.status, 400)
        self.assertEqual(p.res.headers['Content-Type'], 'application/json')
        self.assertIn('Path provided in request did not look valid',
                      p.res.body)

    @vcr.use_cassette('fixtures/proxy_200_valid_path.yaml')
    def test_proxy_200_valid_path(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = '/posts/1'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        self.assertEqual(p.res.status, 200)
        self.assertIn('application/json', p.res.headers['Content-Type'])
        body = json.loads(p.res.body)
        self.assertEqual(body['userId'], 1)

    # No cassette needed as no network request should be sent
    def test_proxy_400_no_handler(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = 'http://badpath.lol/path'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req)
        p.proxy()

        self.assertEqual(p.res.status, 400)
        self.assertEqual(p.res.headers['Content-Type'], 'application/json')
        self.assertIn('Request on_save callback is not set',
                      p.res.body)


class TestProxyInvalidConfig(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https://http'  # bad
        self.conf.port = 443

    def on_save(self, fh, res, conf):
        self.fn = str(uuid.uuid4())
        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.headers['Content-Type'] = 'application/json'
        res.body = json.dumps({'filename': self.fn})

    # No cassette needed as no network request should be sent
    def test_proxy_500_misconfiguration(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = '/posts/1'
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        self.assertEqual(p.res.status, 500)
        self.assertEqual(p.res.headers['Content-Type'], 'application/json')
        self.assertIn('Proxy error while generating URL to request',
                      p.res.body)


class TestServerErrorHandling(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = "localhost"
        self.conf.scheme = "http"
        self.conf.port = 8000

    def make_request(self, method="GET", path_query="/", headers=None):
        req = proxy.Req()
        req.method = method if method else "GET"
        req.path_query = path_query if path_query else "/"
        req.headers = headers if headers else {"Accept": "application/json"}
        return req

    def test_cannot_connect(self):
        """
        Test for "502 Bad Gateway" when the server can't be reached.
        """
        req = self.make_request()

        conf = config.Conf()
        conf.host = "sdproxytest.local"
        conf.scheme = "https"
        conf.port = 8000

        p = proxy.Proxy(conf, req, on_save=callbacks.on_save)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.BAD_GATEWAY)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "could not connect to server")

    def test_server_timeout(self):
        """
        Test for "504 Gateway Timeout" when the server times out.
        """
        class TimeoutProxy(proxy.Proxy):
            """
            Mocks a slow upstream server.

            VCR cassettes cannot represent a request that takes too
            long. This Proxy subclass raises the exception that would
            cause.
            """
            def prep_request(self):
                raise requests.exceptions.Timeout('test timeout')

        req = self.make_request(path_query="/tarpit")
        p = TimeoutProxy(self.conf, req, on_save=callbacks.on_save, timeout=0.00001)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.GATEWAY_TIMEOUT)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "request timed out")

    @vcr.use_cassette("fixtures/proxy_bad_request.yaml")
    def test_bad_request(self):
        """
        Test handling of "400 Bad Request" from the server.
        """
        req = self.make_request(path_query="/bad")
        p = proxy.Proxy(self.conf, req, on_save=callbacks.on_save)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.BAD_REQUEST)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], http.HTTPStatus.BAD_REQUEST.phrase.lower())

    @vcr.use_cassette("fixtures/proxy_unofficial_status.yaml")
    def test_unofficial_status(self):
        """
        Make sure we handle unofficial status codes from the server.

        Should the server ever need to return a status code not in
        Python's http.HTTPStatus, the proxy should still return a
        proper JSON error response with a generic error message.
        """
        req = self.make_request(path_query="/teapot")
        p = proxy.Proxy(self.conf, req, on_save=callbacks.on_save)
        p.proxy()

        self.assertEqual(p.res.status, 418)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "unspecified server error")

    @vcr.use_cassette("fixtures/proxy_internal_server_error.yaml")
    def test_internal_server_error(self):
        """
        Test handling of "500 Internal Server Error" from the server.
        """
        req = self.make_request(path_query="/crash")
        p = proxy.Proxy(self.conf, req, on_save=callbacks.on_save)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.INTERNAL_SERVER_ERROR)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(
            body["error"],
            http.HTTPStatus.INTERNAL_SERVER_ERROR.phrase.lower()
        )

    @vcr.use_cassette("fixtures/proxy_internal_error.yaml")
    def test_internal_error(self):
        """
        Ensure that the proxy returns JSON despite internal errors.
        """
        def bad_on_save(self, fh, res, conf):
            raise Exception("test internal proxy error")

        req = self.make_request()
        p = proxy.Proxy(self.conf, req, on_save=bad_on_save)
        p.proxy()

        self.assertEqual(p.res.status, http.HTTPStatus.INTERNAL_SERVER_ERROR)
        self.assertIn("application/json", p.res.headers["Content-Type"])
        body = json.loads(p.res.body)
        self.assertEqual(body["error"], "internal proxy error")
