#!/usr/bin/env python3

import sys
import json
import securedrop_proxy.proxy as proxy
import uuid
import subprocess

# "read conf"
conf = proxy.Conf()
conf.host = 'jsonplaceholder.typicode.com'
conf.scheme = 'https'
conf.port = 443

# instantiate response object
p = proxy.Proxy(conf)

# timeout?

# read from STDIN
incoming = []
for line in sys.stdin:
    incoming.append(line)

# deserialize incoming request
client_req = None
try:
    client_req = json.loads('\n'.join(incoming))
except json.decoder.JSONDecodeError:
    p.simple_error(400, 'Invalid JSON in request')
    print(json.dumps(p.res.__dict__))
    sys.exit(1)

# build request oject
req = proxy.Req()
try:
    req.method = client_req['method']
    req.path_query = client_req['path_query']
except KeyError:
    p.simple_error(400, 'Missing keys in request')
    print(json.dumps(p.res.__dict__))
    sys.exit(1)

if "headers" in client_req:
    req.headers = client_req['headers']

if "body" in client_req:
    req.body = client_req['body']

def on_save(fh, res):
    fn = str(uuid.uuid4())

    # this will be `qvm-move...` in production
    subprocess.run(["cp", fh.name, "/tmp/{}".format(fn)])

    res.headers['X-Origin-Content-Type'] = res.headers['content-type']
    res.headers['Content-Type'] = 'application/json'
    res.body = json.dumps({'filename': fn })

def on_done(res):
    print(json.dumps(res.__dict__))

# complete proxy object
p.req = req
p.on_save = on_save
p.on_done = on_done
p.proxy()
