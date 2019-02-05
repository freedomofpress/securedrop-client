DEFAULT_GOAL: help
SHELL := /bin/bash

.PHONY: clean
clean:  ## Clean the workspace of generated resources
	@rm -rf build dist *.egg-info .coverage .eggs docs/_build .pytest_cache lib htmlcov .cache && \
		find . \( -name '*.py[co]' -o -name dropin.cache \) -delete && \
		find . \( -name '*.bak' -o -name dropin.cache \) -delete && \
		find . \( -name '*.tgz' -o -name dropin.cache \) -delete && \
		find . -name __pycache__ -print0 | xargs -0 rm -rf

TESTS ?= tests
TESTOPTS ?= -v
.PHONY: test
test: ## Run the application tests
	@TEST_CMD="python -m pytest -v --random-order-bucket=global --cov-config .coveragerc --cov-report html --cov-report term-missing --cov=securedrop_client --cov-fail-under 100 -k-test_alembic.py $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-alembic
test-alembic: ## Run the alembic migration tests
	@python -m pytest -v $(TESTOPTS) tests/test_alembic.py

.PHONY: lint
lint: ## Run the linters
	@flake8 .

.PHONY: check
check: clean lint test test-alembic ## Run the full CI test suite

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
