## Python Client for SecureDrop

### Development

This project uses [pipenv](https://docs.pipenv.org) to manage all dependencies.
This is a Python3 project.

We are using [mypy](http://mypy-lang.org) for type annotation checks.

We cover all the API calls of SecureDrop.

Note: The `get_source` will get an update to take a Source object as an input.

We will also add a bunch of more tests.


### Testing

To test the code, you will need to run the SecureDrop `make dev` command in the same system. The test suite for
this project will test against that development container.

### License: GPLv3+
