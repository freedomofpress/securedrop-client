## securedrop workstation proxy

[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-proxy.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-proxy)

This implements a Qubes RPC <-> HTTP proxy, used to forward requests
from the [securedrop workstation
client](https://github.com/freedomofpress/securedrop-client) to the
[securedrop server](https://github.com/freedomofpress/securedrop).

### try it out

The proxy works by reading a JSON object from STDIN, generating an
HTTP request from that JSON, making that request against the remote
server, then writing a JSON object which represents the remote
server's response to STDOUT. For discussion about the shape of the
request and response objects, see
https://github.com/freedomofpress/securedrop-workstation/issues/107.

This is still development code, not quite ready for integration with the
rest of the securedrop-workstation project. However, it is ready to
be poked at and demonstrated.

#### install requirements

To try the proxy script, first use `pipenv` to create an environment
and install requirements. In the root of the project directory, run

    pipenv install

#### configuration

The proxy script must be run with the path to its configuration file
as its first argument. This repo includes an example configuration
file, at `config-example.yaml`. Configuration consists of the
following values:

- `host` - The hostname of the remote server. Must be set.
- `port` - The port the request should be sent to. Must be set.
- `scheme` - `http` or `https`. Must be set.
- `dev` - A boolean, where `True` indicates we're running in development mode, any other value (or not set) indicates we're running in production. See below for what that means.
- `target_vm` - The name of the VM we should `qvm-move` non-JSON responses to. Must be set if dev is not True.


#### dev vs prod

Configuration includes a "dev" attribute. At this point, the only
difference between dev and production modes is how non-JSON responses
are handled. In prod mode, the content is saved to a local file, then
moved (via `qvm-move`) to the VM indicated by `target_vm`. In dev
mode, the file is not moved off the VM, but is saved as a temporary
file in `/tmp`. In both cases, the response written to STDOUT includes
the name of the new file.

#### tests

Unit tests can be run with `make tests`

#### running

The following commands can be used to demonstrate the proxy.

This demonstrates proxying a request which has an `application/json` response:

    $ cat examples/posts.json | ./sd-proxy.py ./config-example.yaml

This demonstrates proxying a request which has a `text/html` response
and thus is saved to a temp file. The name of the temp file is
included in the result printed to STDOUT- in dev mode, the file can be
read at that name under `/tmp`.

    $ cat examples/html.json | ./sd-proxy.py ./config-example.yaml

Finally, this demonstrates some error handling. The request contains
invalid JSON. The proxy detects that, and prints an error message
(still a valid proxy response).

    $ cat examples/bad.json | ./sd-proxy.py ./config-example.yaml

#### Qubes integration

Until we determine how we wish to package and install this script,
demonstrating the proxy in a Qubes environment is a somewhat manual
process.

First, determine which of your VMs will be acting as the proxy VM
(where this code will be running), and which will be acting as the
client VM (where the client code will be running). For the purposes of
this documentation, we assume the client is running in
`securedrop-client`, and the proxy is running in `seuredrop-proxy`.

Edit `qubes/securedrop.Proxy` to reflect the path to `entrypoint.sh`
in this repo. Run `make install`, which will move `securedrop.Proxy`
(the qubes-rpc "server path definition" file) into place in
`/etc/qubes-rpc/`.

On `dom0`, create the file `/etc/qubes-rpc/policy/securedrop.Proxy`
with the contents:

    securedrop-client securedrop-proxy allow
    $anyvm $anyvm deny

(replacing the VM names with the correct source and destination names
for your environment)

Also in `dom0`, edit `/etc/qubes-rpc/policy/qubes.Filecopy`, to add
near the top:

    securedrop-proxy securedrop-client allow

(again replacing the VM names with the correct source and destination
names for your environment). This allows non-JSON responses to be
moved to the client VM using Qubes' native inter-VM file copy service.

Copy `config-example.yaml` to `config.yaml`, and edit it to reflect
your situation- check that `target_vm` is set to the correct client VM
name, and assure that `dev` is `False`. This documentation assumes
you've left `host` set to `jsonplaceholder.typicode.com`.

Now on the client VM you should be able to do:

    $ echo '{"method":"GET","path_query":"/posts?userId=1"}' | /usr/lib/qubes/qrexec-client-vm securedrop-client securedrop.Proxy

You should see a successful JSON response as returned by the remote server.

Try now

    $ echo '{"method":"GET","path_query":""}' | /usr/lib/qubes/qrexec-client-vm securedrop-client securedrop.Proxy

If you have configured everything correctly, you should see a JSON
response which include a `body` which looks like:

    { ...
      "body": "{\"filename\": \"7463c589-92d2-46ba-845f-3ace2587916d\"}"
    }

If you look in `~/QubesIncoming/securedrop-proxy`, you should see a
new file with that name. The content of that file will be the content
returned by the remote server.

Finally, try invoking an error. Provide an invalid JSON request, and
notice you receive a `400` response from the proxy:

    $ echo '[INVALID' | /usr/lib/qubes/qrexec-client-vm securedrop-client securedrop.Proxy
    {"body": "{\"error\": \"Invalid JSON in request\"}", "version": "0.1.1", "status": 400, "headers": {"Content-Type": "application/json"}}
