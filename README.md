# securedrop-client
[![CircleCI](https://circleci.com/gh/freedomofpress/securedrop-client.svg?style=svg)](https://circleci.com/gh/freedomofpress/securedrop-client)

Qt-based client for working with SecureDrop submissions on the SecureDrop Qubes Workstation

## Getting Started

Set up a Python 3 virtual environment and set up dependencies:

```
mkvirtualenv --python=python3 securedropclient
pip install -r requirements/requirements.txt
pip install -r requirements/requirements-dev.txt
```

## Run tests

```
python -m unittest
```

## Generate and run database migrations

```
alembic revision --autogenerate -m "describe your revision here"
alembic upgrade head
```
