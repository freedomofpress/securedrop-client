import json

from securedrop_proxy import callbacks
from securedrop_proxy import proxy


def __main__(incoming, p):
    # deserialize incoming request
    client_req = None
    try:
        client_req = json.loads(incoming)
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

    # complete proxy object
    p.req = req
    p.on_save = callbacks.on_save
    p.on_done = callbacks.on_done
    p.proxy()
