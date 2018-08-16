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

        res.headers['X-Origin-Content-Type'] = res.headers['content-type']
        res.headers['Content-Type'] = 'application/json'
        res.body = json.dumps({'filename': self.fn })

    def test_400_if_callback_not_set(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy()
        p.proxy()

        assert p.res.status == 400

    @vcr.use_cassette('fixtures/basic_proxy_functionality.yaml')
    def test_proxy_basic_functionality(self):
        req = proxy.Req()
        req.method = 'GET'
        req.path_query = ''
        req.headers = {'Accept': 'application/json'}

        p = proxy.Proxy(self.conf, req, self.on_save)
        p.proxy()

        assert p.res.status == 200
        assert p.res.body == json.dumps({'filename': self.fn })

        # This is the way to verify the 'content-type' header
        assert p.res.headers['_store']['content-type'][1] == 'application/json'

        # But I want to do this
        # assert p.res.headers['Content-Type'] == 'application/json'
