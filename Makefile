DEFAULT_GOAL: help
SHELL := /bin/bash

.PHONY: mypy
mypy: ## Run static type checker
	@mypy --ignore-missing-imports securedrop_client
	@# Add files that are 100% typed to the below call (eventually just the below line will run so that code without static type hints will fail CI)
	@mypy --ignore-missing-imports \
		--disallow-incomplete-defs \
		--disallow-untyped-defs \
		securedrop_client/db.py \
		securedrop_client/crypto.py \
		securedrop_client/config.py \
		securedrop_client/gui/__init__.py \
		securedrop_client/resources/__init__.py \
		securedrop_client/storage.py \
		securedrop_client/queue.py \
		securedrop_client/api_jobs/__init__.py \
		securedrop_client/api_jobs/base.py \
		securedrop_client/api_jobs/downloads.py \
		securedrop_client/api_jobs/uploads.py

.PHONY: clean
clean:  ## Clean the workspace of generated resources
	@rm -rf .mypy_cache build dist *.egg-info .coverage .eggs docs/_build .pytest_cache lib htmlcov .cache && \
		find . \( -name '*.py[co]' -o -name dropin.cache \) -delete && \
		find . \( -name '*.bak' -o -name dropin.cache \) -delete && \
		find . \( -name '*.tgz' -o -name dropin.cache \) -delete && \
		find . -name __pycache__ -print0 | xargs -0 rm -rf

TESTS ?= tests
FTESTS ?= tests/functional
TESTOPTS ?= -v
.PHONY: test
test: ## Run the application tests in parallel (for rapid development)
	@TEST_CMD="python -m pytest -v -n 4 --ignore=$(FTESTS) --cov-config .coveragerc --cov-report html --cov-report term-missing --cov=securedrop_client --cov-fail-under 100 $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-random
test-random: ## Run the application tests in random order
	@TEST_CMD="python -m pytest -v --ignore=$(FTESTS) --random-order-bucket=global --cov-config .coveragerc --cov-report html --cov-report term-missing --cov=securedrop_client --cov-fail-under 100 $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-functional
test-functional : ## Run the functional tests in random order.
	@TEST_CMD="python -m pytest -v --random-order-bucket=global $(TESTOPTS) $(FTESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: lint
lint: ## Run the linters
	@flake8 securedrop_client tests

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	pip install --upgrade safety && \
		for req_file in `find . -type f -name '*requirements.txt'`; do \
			echo "Checking file $$req_file" \
			&& safety check --full-report -r $$req_file \
			&& echo -e '\n' \
			|| exit 1; \
		done

# Bandit is a static code analysis tool to detect security vulnerabilities in Python applications
# https://wiki.openstack.org/wiki/Security/Projects/Bandit
.PHONY: bandit
bandit: ## Run bandit with medium level excluding test-related folders
	pip install --upgrade pip && \
	pip install --upgrade bandit && \
	bandit -ll --recursive . --exclude ./tests,./.venv

.PHONY: check
check: clean bandit lint mypy test-random test-functional ## Run the full CI test suite

.PHONY: update-pip-requirements
update-pip-requirements: ## Updates all Python requirements files via pip-compile.
	pip-compile --generate-hashes --allow-unsafe --output-file dev-requirements.txt requirements.in dev-requirements.in
	pip-compile --generate-hashes --output-file requirements.txt requirements.in

# Explaination of the below shell command should it ever break.
# 1. Set the field separator to ": ##" and any make targets that might appear between : and ##
# 2. Use sed-like syntax to remove the make targets
# 3. Format the split fields into $$1) the target name (in blue) and $$2) the target descrption
# 4. Pass this file as an arg to awk
# 5. Sort it alphabetically
# 6. Format columns with colon as delimiter.
.PHONY: help
help: ## Print this message and exit.
	@printf "Makefile for developing and testing the SecureDrop client.\n"
	@printf "Subcommands:\n\n"
	@awk 'BEGIN {FS = ":.*?## "} /^[0-9a-zA-Z_-]+:.*?## / {printf "\033[36m%s\033[0m : %s\n", $$1, $$2}' $(MAKEFILE_LIST) \
		| sort \
		| column -s ':' -t
