import json
import subprocess
import vcr
import unittest
import uuid

from securedrop_proxy import proxy
from securedrop_proxy import config


class TestProxy(unittest.TestCase):
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
        res.body = json.dumps({'filename': self.fn })

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

        self.assertEquals(p.res.status, 400)

    @vcr.use_cassette('fixtures/basic_proxy_functionality.yaml')
    def test_proxy_basic_functionality(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        self.assertEquals(p.res.status, 200)
        self.assertEquals(p.res.body, json.dumps({'filename': self.fn }))
        self.assertEquals(p.res.headers['Content-Type'], 'application/json')

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

        self.assertEquals(p.res.status, 404)
        self.assertEquals(p.res.headers['Content-Type'], 'application/json')
