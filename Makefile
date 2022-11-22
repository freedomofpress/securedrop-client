.PHONY: all
all: help

# Default to plain "python3"
PYTHON ?= python3
VERSION_CODENAME ?= bullseye

.PHONY: venv
venv: hooks ## Provision a Python 3 virtualenv for development on Linux
	$(PYTHON) -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-${VERSION_CODENAME}-requirements.txt"
	@echo "#################"
	@echo "Make sure to run: source .venv/bin/activate"

.PHONY: venv-sdw
venv-sdw: hooks ## Provision a Python 3 virtualenv for development on a prod-like system that has installed dependencies specified in https://github.com/freedomofpress/securedrop-builder/blob/main/securedrop-client/debian/control
	$(PYTHON) -m venv .venv --system-site-packages
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-sdw-requirements.txt"
	@echo "#################"
	@echo "Virtualenv with Debian system-packages is complete."
	@echo "Make sure to install the apt packages for system Qt."
	@echo "Then run: source .venv/bin/activate"

.PHONY: venv-mac
venv-mac: hooks ## Provision a Python 3 virtualenv for development on macOS
	$(PYTHON) -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install -r "requirements/dev-mac-requirements.in"
	@echo "#################"
	@echo "Make sure to run: source .venv/bin/activate"

HOOKS_DIR=.githooks

.PHONY: hooks
hooks:  ## Configure Git to use the hooks provided by this repository.
	git config core.hooksPath "$(HOOKS_DIR)"

SEMGREP_FLAGS := --exclude "tests/" --error --strict --verbose

.PHONY: semgrep
semgrep:semgrep-community semgrep-local  ## Run semgrep with both semgrep.dev community and local rules

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
	@isort --skip-glob .venv ./

.PHONY: check-isort
check-isort: ## Check Python import organization with isort
	@isort --skip-glob .venv --check-only --diff ./

.PHONY: mypy
mypy: ## Run static type checker
	@mypy --ignore-missing-imports \
		--disallow-incomplete-defs \
		--disallow-untyped-defs \
		--show-error-codes \
		--warn-unreachable \
		--warn-unused-ignores \
		securedrop_client \
		*.py

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
RANDOM_SEED ?= $(shell bash -c 'echo $$RANDOM')

.PHONY: test
test: ## Run the application tests in parallel (for rapid development)
	@TEST_CMD="python -m pytest -v -n 4 --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-random
test-random: ## Run the application tests in random order
	@TEST_CMD="python -m pytest -v --junitxml=test-results/junit.xml --random-order-bucket=global --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
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
	@TEST_CMD="python -m pytest -v -n 4 --random-order-bucket global --random-order-seed=$(RANDOM_SEED) $(FTESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run --server-args="-screen 0, 1680x1050x24" -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

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

.PHONY: dev-requirements
dev-requirements:  ## Update dev-*requirements.txt files if pinned versions do not comply with the dependency specifications in dev-*requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-bullseye-requirements.txt requirements/dev-bullseye-requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-bookworm-requirements.txt requirements/dev-bookworm-requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-sdw-requirements.txt requirements/dev-sdw-requirements.in

.PHONY: update-dev-dependencies
update-dev-dependencies:  ## Update dev requirements in case there are newer versions of packages or updates to prod dependencies
	if test -f "requirements/dev-bullseye-requirements.txt"; then rm -r requirements/dev-bullseye-requirements.txt; fi
	if test -f "requirements/dev-bookworm-requirements.txt"; then rm -r requirements/dev-bookworm-requirements.txt; fi
	if test -f "requirements/dev-sdw-requirements.txt"; then rm -r requirements/dev-sdw-requirements.txt; fi
	$(MAKE) dev-requirements

.PHONY: requirements
requirements:  ## Update *requirements.txt files if pinned versions do not comply with the dependency specifications in *requirements.in
	pip-compile --generate-hashes --output-file requirements/requirements.txt requirements/requirements.in
	$(MAKE) dev-requirements

# Explanation of the below shell command should it ever break.
# 1. Set the field separator to ": ##" and any make targets that might appear between : and ##
# 2. Use sed-like syntax to remove the make targets
# 3. Format the split fields into $$1) the target name (in blue) and $$2) the target description
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

.PHONY: version
version:
	@python -c "import securedrop_client; print(securedrop_client.__version__)"


.PHONY: docs
docs:  ## Generate browsable documentation and call/caller graphs (requires Doxygen and Graphviz)
	@which doxygen >> /dev/null || { echo "doxygen(1) is not available in your \$$PATH.  Is it installed?"; exit 1; }
	@which dot >> /dev/null || { echo "Graphviz's dot(1) is not available in your \$$PATH.  Is it installed?"; exit 1; }
	@doxygen
	@echo "Now open \"$(PWD)/docs/html/index.html\" in your browser."

##############
#
# Localization
#
##############

LOCALE_DIR=securedrop_client/locale
POT=${LOCALE_DIR}/messages.pot
VERSION=$(shell python -c "import securedrop_client; print(securedrop_client.__version__)")

.PHONY: check-strings
check-strings: ## Check that the translation catalog is up to date with source code
	@make extract-strings
	@git diff --quiet ${LOCALE_DIR} || { echo "Translation catalog is out of date. Please run \"make extract-strings\" and commit the changes."; exit 1; }

.PHONY: extract-strings
extract-strings: ## Extract translatable strings from source code
	@make --always-make ${POT}

# Derive POT from sources.
$(POT): securedrop_client
	@echo "updating catalog template: $@"
	@mkdir -p ${LOCALE_DIR}
	@pybabel extract \
		--charset=utf-8 \
		--output=${POT} \
		--project="SecureDrop Client" \
		--version=${VERSION} \
		--msgid-bugs-address=securedrop@freedom.press \
		--copyright-holder="Freedom of the Press Foundation" \
		--add-comments="Translators:" \
		--strip-comments \
		--add-location=never \
		--no-wrap \
		$^
	@sed -i -e '/^"POT-Creation-Date/d' ${POT}

