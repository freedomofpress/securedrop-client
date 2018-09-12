# securedrop-client
[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-client.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-client)

Qt-based client for working with SecureDrop submissions on the SecureDrop Qubes Workstation

## Getting Started

Set up a Python 3 virtual environment and set up dependencies:

```
pipenv install --dev
pipenv shell
```

## Run tests

```
make test
```

## Generate and run database migrations

```
alembic revision --autogenerate -m "describe your revision here"
alembic upgrade head
```
