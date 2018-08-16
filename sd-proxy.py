#!/usr/bin/env python3

# The sd-proxy RPC script triggered by qubes RPC.

# This script is executed by `/etc/qubes-rpc/sd-proxy`. It must be
# called with exactly one argument: the path to its config file. See
# the README for configuration options.

import sys
import json
import securedrop_proxy.proxy as proxy
import uuid
import subprocess
import securedrop_proxy.config as config

# a fresh, new proxy object
p = proxy.Proxy()

# set up an error handler early, so we can use it during
# configuration, etc
def err_on_done(res):
    print(json.dumps(res.__dict__))
    sys.exit(1)

p.on_done = err_on_done

# path to config file must be at argv[1]
if len(sys.argv) != 2:
    p.simple_error(500, 'sd-proxy script not called with path to configuration file')
    p.on_done(p.res)
    print(json.dumps(p.res.__dict__))

# read config. `read_conf` will call `p.on_done` if there is a config
# problem, and will return a Conf object on success.
conf_path = sys.argv[1]
p.conf = config.read_conf(conf_path, p)

# read user request from STDIN
incoming = []
for line in sys.stdin:
    incoming.append(line)

# deserialize incoming request
client_req = None
try:
    client_req = json.loads('\n'.join(incoming))
except json.decoder.JSONDecodeError:
    p.simple_error(400, 'Invalid JSON in request')
    p.on_done(p.res)

# build request oject
req = proxy.Req()
try:
    req.method = client_req['method']
    req.path_query = client_req['path_query']
except KeyError:
    p.simple_error(400, 'Missing keys in request')
    p.on_done(p.res)

if "headers" in client_req:
    req.headers = client_req['headers']

if "body" in client_req:
    req.body = client_req['body']

# callback for handling non-JSON content. in production-like
# environments, we want to call `qvm-move-to-vm` (and expressly not
# `qvm-move`, since we want to include the destination VM name) to
# move the content to the target VM. for development and testing, we
# keep the file on the local VM.
#
# In any case, this callback mutates the given result object (in
# `res`) to include the name of the new file, or to indicate errors.
def on_save(fh, res):
    fn = str(uuid.uuid4())

    try:
        if p.conf.dev is True:
            subprocess.run(["cp", fh.name, "/tmp/{}".format(fn)])
        else:
            subprocess.run(["cp", fh.name, "/tmp/{}".format(fn)])
            subprocess.run(['qvm-move-to-vm', p.conf.target_vm, "/tmp/{}".format(fn)])
    except Exception:
        res.status = 500
        res.headers['Content-Type'] = 'application/json'
        res.headers['X-Origin-Content-Type'] = res.headers['content-type']
        res.body = json.dumps({"error": "Unhandled error while handling non-JSON content, sorry"})
        return

    res.headers['X-Origin-Content-Type'] = res.headers['content-type']
    res.headers['Content-Type'] = 'application/json'
    res.body = json.dumps({'filename': fn })

# new on_done handler (which, in practice, is largely like the early
# one)
def on_done(res):
    print(json.dumps(res.__dict__))

# complete proxy object
p.req = req
p.on_save = on_save
p.on_done = on_done
p.proxy()
