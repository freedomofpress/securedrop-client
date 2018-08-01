## Python Client for SecureDrop

Note: This is not an official recommended project.

### Development

This project uses [pipenv](https://docs.pipenv.org) to manage all dependencies.
This is a Python3 project.

We are using [mypy](http://mypy-lang.org) for type annotation checks.

### Code formatting

We are using [Black](https://black.readthedocs.io/en/stable/) tool for code formatting. There is a dockerfile
in the repository, which can be used to run Black on the code.

```
docker build -t kdas/black -f Dockerfile.black
docker run --rm -v $PWD:/home/kdas/workplace kdas/black black .
```

Note: The dockerfile still needs work.


This is work in progress. The following API(s) are still missing.

- post reply to source
- download a submission

We will also add a bunch of more tests.


### Testing

To test the code, you will need to run the SecureDrop `make dev` command in the same system. The test suite for
this project will test against that development container.

### License: GPLv3+