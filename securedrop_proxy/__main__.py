import proxy
import json
import subprocess
import uuid

conf = proxy.Conf()
conf.host = 'jsonplaceholder.typicode.com'
conf.scheme = 'https'
conf.port = 443

def on_save(fh, res):

    fn = str(uuid.uuid4())

    # this will be `qvm-move...` in production
    subprocess.run(["cp", fh.name, "/tmp/{}".format(fn)])

    res.headers['X-Origin-Content-Type'] = res.headers['content-type']
    res.headers['Content-Type'] = 'application/json'
    res.body = json.dumps({'filename': fn })

# does it work at all
req = proxy.Req()
req.method = 'GET'
req.path_query = ''
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status)
print(p.res.headers)
print(p.res.version)
print(p.res.body)

# params
req = proxy.Req()
req.method = 'GET'
req.path_query = '/posts?userId=1'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status)
#print(res.headers)
print(p.res.version)
print(json.loads(p.res.body.decode()))


# path
req = proxy.Req()
req.method = 'GET'
req.path_query = '/posts/1'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status) # 200
print(p.res.version)
print(json.loads(p.res.body.decode()))


# 404
req = proxy.Req()
req.method = 'GET'
req.path_query = '/notfound'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status) # 404
print(p.res.headers)
print(p.res.version)
print(p.res.body) # {}


# 400 bad path
req = proxy.Req()
req.method = 'GET'
req.path_query = 'http://badpath.lol/path'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status) # 400
print(p.res.headers)
print(p.res.version)
print(p.res.body) # {'error': 'Path provided in request did not look valid'}

# 400 no handler
req = proxy.Req()
req.method = 'GET'
req.path_query = 'http://badpath.lol/path'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, None)
p.proxy()

print(p.res.status) # 400
print(p.res.headers)
print(p.res.version)
print(p.res.body) # {'error': 'Request callback is not set.'}


# 500 proxy error (in this case, misconfiguration)
conf = proxy.Conf()
conf.host = 'jsonplaceholder.typicode.com'
conf.scheme = 'https://http' # bad
conf.port = 443

req = proxy.Req()
req.method = 'GET'
req.path_query = '/posts/1'
req.headers = {'Accept': 'application/json'}

p = proxy.Proxy(conf, req, on_save)
p.proxy()

print(p.res.status) # 500
print(p.res.headers)
print(p.res.version)
print(p.res.body) # {'error': 'Proxy error while generating URL to request'}
