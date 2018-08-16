import json
import subprocess
import vcr
import unittest
import uuid

from securedrop_proxy import proxy
from securedrop_proxy import config


class TestProxyValidConfig(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https'
        self.conf.port = 443

    def on_save(self, fh, res):

        self.fn = str(uuid.uuid4())

        # this will be `qvm-move...` in production
        subprocess.run(["cp", fh.name, "/tmp/{}".format(self.fn)])

        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.headers['Content-Type'] = 'application/json'
        res.body = json.dumps({'filename': self.fn})

    def on_done(self, res):
        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.headers['Content-Type'] = 'application/json'

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
        self.assertIn('Request callback is not set',
                      p.res.body)


class TestProxyInvalidConfig(unittest.TestCase):
    def setUp(self):
        self.conf = config.Conf()
        self.conf.host = 'jsonplaceholder.typicode.com'
        self.conf.scheme = 'https://http'  # bad
        self.conf.port = 443

    def on_save(self, fh, res):
        self.fn = str(uuid.uuid4())

        # this will be `qvm-move...` in production
        subprocess.run(["cp", fh.name, "/tmp/{}".format(self.fn)])

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
