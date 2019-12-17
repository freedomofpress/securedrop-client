import json
import logging

from securedrop_proxy import callbacks
from securedrop_proxy import proxy


logger = logging.getLogger(__name__)


def __main__(incoming, p):
    '''
    Deserialize incoming request in order to build and send a proxy request.
    '''
    logging.debug('Creating request to be sent by proxy')

    client_req = None
    try:
        client_req = json.loads(incoming)
    except json.decoder.JSONDecodeError as e:
        logging.error(e)
        p.simple_error(400, 'Invalid JSON in request')
        p.on_done(p.res)
        return

    req = proxy.Req()
    try:
        req.method = client_req['method']
        req.path_query = client_req['path_query']
    except KeyError as e:
        logging.error(e)
        p.simple_error(400, 'Missing keys in request')
        p.on_done(p.res)

    if "headers" in client_req:
        req.headers = client_req['headers']

    if "body" in client_req:
        req.body = client_req['body']

    p.req = req
    if p.on_save is None:
        p.on_save = callbacks.on_save
    p.proxy()
