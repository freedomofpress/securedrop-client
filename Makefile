.PHONY: all
all: help

.PHONY: venv
venv: ## Provision a Python 3 virtualenv for **development**
	python3 -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-requirements.txt"

SEMGREP_FLAGS := --exclude "tests/" --error --strict --verbose

.PHONY: semgrep
semgrep:semgrep-community semgrep-local

.PHONY: semgrep-community
semgrep-community:
	@echo "Running semgrep with semgrep.dev community rules..."
	@semgrep $(SEMGREP_FLAGS) --config "p/r2c-security-audit"

.PHONY: semgrep-local
semgrep-local:
	@echo "Running semgrep with local rules..."
	@semgrep $(SEMGREP_FLAGS) --config ".semgrep"

.PHONY: black
black: ## Format Python source code with black
	@black ./

.PHONY: check-black
check-black: ## Check Python source code formatting with black
	@black --check --diff ./

.PHONY: isort
isort: ## Run isort to organize Python imports
	@isort --recursive ./

.PHONY: check-isort
check-isort: ## Check Python import organization with isort
	@isort --check-only --diff --recursive ./

.PHONY: mypy
mypy: ## Run static type checker on all .py files in project
	@mypy --ignore-missing-imports \
		*.py \
		**/*.py \
		securedrop_client/**/*.py \
		tests/**/*.py

.PHONY: clean
clean:  ## Clean the workspace of generated resources
	@rm -rf .mypy_cache build dist *.egg-info .coverage .eggs docs/_build .pytest_cache lib htmlcov .cache && \
		find . \( -name '*.py[co]' -o -name dropin.cache \) -delete && \
		find . \( -name '*.bak' -o -name dropin.cache \) -delete && \
		find . \( -name '*.tgz' -o -name dropin.cache \) -delete && \
		find . -name __pycache__ -print0 | xargs -0 rm -rf

TESTS ?= tests
ITESTS ?= tests/integration
FTESTS ?= tests/functional
TESTOPTS ?= -v --cov-config .coveragerc --cov-report html --cov-report term-missing --cov=securedrop_client --cov-fail-under 100

.PHONY: test
test: ## Run the application tests in parallel (for rapid development)
	@TEST_CMD="python -m pytest -v -n 4 --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-random
test-random: ## Run the application tests in random order
	@TEST_CMD="python -m pytest -v --random-order-bucket=global --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-integration
test-integration: ## Run the integration tests
	@TEST_CMD="python -m pytest -v -n 4 $(ITESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-functional
test-functional: ## Run the functional tests
	@./test-functional.sh

.PHONY: lint
lint: ## Run the linters
	@flake8 securedrop_client tests

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	pip install --upgrade safety && \
		for req_file in `find . -type f -wholename '*requirements.txt'`; do \
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
check: clean check-black check-isort semgrep bandit lint mypy test-random test-integration test-functional ## Run the full CI test suite

.PHONY: sync-requirements
sync-requirements:  ## Update dev-requirements.txt to pin to the same versions of prod dependencies
	rm -r requirements/dev-requirements.txt && cp requirements/requirements.txt requirements/dev-requirements.txt
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-requirements.txt requirements/requirements.in requirements/dev-requirements.in

.PHONY: requirements
requirements:  ## Update *requirements.txt files if pinned versions do not comply with the dependency specifications in *requirements.in
	pip-compile --generate-hashes --output-file requirements/requirements.txt requirements/requirements.in
	$(MAKE) sync-requirements

.PHONY: update-dependency
update-dependency:  ## Add or upgrade a package to the latest version that complies with the dependency specifications in requirements.in
	pip-compile --generate-hashes --upgrade-package $(PACKAGE) --output-file requirements/requirements.txt requirements/requirements.in
	$(MAKE) sync-requirements

.PHONY: update-dev-only-dependencies
update-dev-only-dependencies:  ## Update dev-requirements.txt to pin to the latest versions of dev-only dependencies that comply with the dependency specifications in dev-requirements.in
	$(MAKE) sync-requirements
	@while read line; do \
		pip-compile --allow-unsafe --generate-hashes --upgrade-package $file --output-file requirements/dev-requirements.txt requirements/requirements.in requirements/dev-requirements.in; \
	done < 'requirements/dev-requirements.in'

.PHONY: update-pip-requirements
update-pip-requirements: ## Updates all Python requirements files via pip-compile for Linux.
	pip-compile --verbose --rebuild --generate-hashes --annotate --allow-unsafe --output-file "requirements/dev-requirements.txt" "requirements/requirements.in" "requirements/dev-requirements.in"
	pip-compile --verbose --rebuild --generate-hashes --annotate --output-file "requirements/requirements.txt" "requirements/requirements.in"

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
