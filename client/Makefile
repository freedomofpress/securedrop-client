.PHONY: all
all: help

# We prefer to use python3.11 if it's available, especially on arm64 based Macs,
# but we're also OK with just python3 if that's all we've got
PYTHON := $(if $(shell bash -c "command -v python3.11"), python3.11, python3)

SEMGREP_FLAGS := --exclude "tests/" --error --strict --verbose

doxygen:
	@which doxygen >> /dev/null || { echo "doxygen(1) is not available in your \$$PATH.  Is it installed?"; exit 1; }

graphviz:
	@which dot >> /dev/null || { echo "Graphviz's dot(1) is not available in your \$$PATH.  Is it installed?"; exit 1; }

.PHONY: graph-code
graph-code: doxygen graphviz  ## Generate browsable documentation and call/caller graphs (requires Doxygen and Graphviz).
	@doxygen
	@echo "Now open \"$(PWD)/docs/html/index.html\" in your browser."

.PHONY: graph-db
graph-db: graphviz  ## Generate an ERD of the Client's database models (requires Graphviz).
	@poetry run paracelsus graph --format dot > docs/db.dot
	@dot -Tpng docs/db.dot > docs/db.png
	@echo "Now open \"$(PWD)/docs/db.png\"."

.PHONY: semgrep
semgrep:semgrep-community semgrep-local  ## Run semgrep with both semgrep.dev community and local rules

.PHONY: semgrep-community
semgrep-community:
	@echo "Running semgrep with semgrep.dev community rules..."
	@poetry run semgrep $(SEMGREP_FLAGS) --config "p/r2c-security-audit"

.PHONY: semgrep-local
semgrep-local:
	@echo "Running semgrep with local rules..."
	@poetry run semgrep $(SEMGREP_FLAGS) --config ".semgrep"

.PHONY: mypy
mypy: ## Run static type checker
	@MYPYPATH="stubs" poetry run mypy --ignore-missing-imports \
		--disallow-incomplete-defs \
		--disallow-untyped-defs \
		--show-error-codes \
		--warn-unreachable \
		--warn-unused-ignores \
		scripts/*.py \
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
STESTS ?= tests/sdk
TESTOPTS ?= -v --cov-config .coveragerc --cov-report html --cov-report term-missing --cov=securedrop_client --cov-fail-under 90
RANDOM_SEED ?= $(shell bash -c 'echo $$RANDOM')

.PHONY: test
test: ## Run the application tests (for rapid development)
	@TEST_CMD="poetry run pytest -v --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
		source scripts/setup-tmp-directories.sh; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-random
test-random: ## Run the application tests in random order
	@TEST_CMD="poetry run pytest -v --junitxml=test-results/junit.xml --random-order-bucket=global --ignore=$(FTESTS) --ignore=$(ITESTS) $(TESTOPTS) $(TESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-integration
test-integration: ## Run the integration tests
	@TEST_CMD="poetry run pytest -v $(ITESTS)" ; \
		if command -v xvfb-run > /dev/null; then \
		xvfb-run -a $$TEST_CMD ; else \
		$$TEST_CMD ; fi

.PHONY: test-functional
test-functional: ## Run the functional tests
	@./test-functional.sh

.PHONY: test-sdk
test-sdk: ## Run just the sdk tests
	@poetry run pytest -v $(STESTS)

.PHONY: regenerate-sdk-cassettes
regenerate-sdk-cassettes:
	@echo "Building securedrop-proxy (if not already done)..."
	@$(MAKE) -C ../proxy build
	@echo "Checking if a development server is available to regenerate cassettes..."
	@echo "NB. It should be a fresh development server via \"make dev\", with no other data!  HTTP requests and responses will be recorded unredacted, including credentials and tokens."
	@curl http://localhost:8080/metadata
	@rm -fr tests/sdk/data/
	@make test-sdk

.PHONY: lint
lint: mypy semgrep ## Run all linters

.PHONY: check
check: clean lint test-random test-integration test-functional ## Run the full CI test suite

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
	@poetry run python -c "import securedrop_client; print(securedrop_client.__version__)"

##############
#
# Localization
#
##############

LOCALE_DIR=securedrop_client/locale
POT=${LOCALE_DIR}/messages.pot

.PHONY: check-strings
check-strings: ## Check that the translation catalog is up to date with source code
	@make extract-strings
	@git diff --ignore-matching-lines='^"Generated-By: Babel' --exit-code ${LOCALE_DIR} || { echo "Translation catalog is out of date. Please run \"make extract-strings\" and commit the changes."; exit 1; }

.PHONY: extract-strings
extract-strings: ## Extract translatable strings from source code
	@make --always-make ${POT}

# Derive POT from sources.
$(POT): securedrop_client
	@echo "updating catalog template: $@"
	@mkdir -p ${LOCALE_DIR}
	@poetry run pybabel extract \
		-F babel.cfg \
		--charset=utf-8 \
		--output=${POT} \
		--project="SecureDrop Client" \
		--msgid-bugs-address=securedrop@freedom.press \
		--copyright-holder="Freedom of the Press Foundation" \
		--add-comments="Translators:" \
		--strip-comments \
		--add-location=never \
		--no-wrap \
		$^
	@sed -i -e '/^"POT-Creation-Date/d' ${POT}

.PHONY: verify-mo
verify-mo: ## Verify that all gettext machine objects (.mo) are reproducible from their catalogs (.po).
	@TERM=dumb poetry run scripts/verify-mo.py ${LOCALE_DIR}/*
	@# All good; now clean up.
	@git restore "${LOCALE_DIR}/**/*.po"

# Install dependencies in CI
# Note, we don't actually need libqt5x11extras5, but it pulls in all
# the correct dependencies for the PyQt5 wheels.
ci-install-deps:
	apt-get install --yes xvfb sqlite3 locales libqt5x11extras5 python3-tk
	echo "en_US ISO-8859-1" >> /etc/locale.gen
	echo "en_US UTF-8" >> /etc/locale.gen
	locale-gen
