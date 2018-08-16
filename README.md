## securedrop workstation proxy

This implements a Qubes RPC <-> HTTP proxy, used to forward requests
from the [securedrop workstation
client](https://github.com/freedomofpress/securedrop-client) to the
[securedrop server](https://github.com/freedomofpress/securedrop).

### try it out

The proxy works by reading a JSON object from STDIN, generating an
HTTP request from the JSON it's read, executing that request, then
writing to STDOUT a JSON object which represents the remote server's
response. For discussion about the shape of the request and response
objects, see
https://github.com/freedomofpress/securedrop-workstation/issues/107.

#### install requirements

This is still development code, and not ready for integration with the
rest of the securedrop-workstation project. That said, it is ready to
be poked at tested.

To try the proxy script, first use `pipenv` to create an environment
and install requirements. In the root of the project directoy, run

    pipenv install

#### configuration

The proxy script must be run with the path to its configuration file
as its first argument. This repo includes an example configuration
file, at `config-example.yaml`. Configuration consists of the
following values:

    * host: the hostname of the remote server. must be set.
    * port: the port the request should be sent to. must be set.
    * scheme: http or https. must be set.
    * dev: a boolean- True indicates we're running in development mode, any other value (or not set) indicates we're running in production. See below for what that means.
    * target_vm: the name of the VM we should `qvm-move` non-JSON responses to. must be set if dev is not True


#### dev vs prod

Configuration includes a "dev" attribute. At this point, the only
difference between dev and production modes is how non-JSON responses
are handled. In prod mode, the content is saved to a local file, then
moved (via `qvm-move`) to the VM indicated in `target_vm`. In dev
mode, the file is not moved off the VM, but is saved as a temporary
file in `/tmp`. In both cases, the response written to STDOUT includes
the name of the new file.

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
