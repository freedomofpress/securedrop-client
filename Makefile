.PHONY: all
all: help

.PHONY: venv-debian
venv-debian: ## Provision a Python 3 virtualenv for development on a prod-like system that has installed dependencies specified in https://github.com/freedomofpress/securedrop-debian-packaging/blob/main/securedrop-client/debian/control
	python3 -m venv .venv-debian --system-site-packages
	.venv-debian/bin/pip install --upgrade pip wheel
	.venv-debian/bin/pip install --require-hashes -r "requirements/dev-requirements-debian.txt"
	@echo "#################"
	@echo "Virtualenv with Debian system-packages is complete."
	@echo "Make sure to install the apt packages for system Qt."
	@echo "Then run: source .venv-debian/bin/activate"

.PHONY: venv
venv: ## Provision a Python 3 virtualenv for development on Linux
	python3 -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-requirements.txt"
	@echo "#################"
	@echo "Make sure to run: source .venv/bin/activate"

.PHONY: venv-mac
venv-mac: ## Provision a Python 3 virtualenv for development on macOS
	python3 -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-mac-requirements.txt"
	@echo "#################"
	@echo "Make sure to run: source .venv/bin/activate"

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
	@isort --skip-glob .venv-debian ./

.PHONY: check-isort
check-isort: ## Check Python import organization with isort
	@isort --skip-glob .venv-debian --check-only --diff ./

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
	bandit -ll --recursive . --exclude ./tests,./.venv,./.venv-debian

.PHONY: check
check: clean check-black check-isort semgrep bandit lint mypy test-random test-integration test-functional ## Run the full CI test suite

.PHONY: sync-requirements
sync-requirements:  ## Update dev-requirements.txt to pin to the same versions of prod dependencies
	if test -f "requirements/dev-requirements.txt"; then rm -r requirements/dev-requirements.txt; fi
	if test -f "requirements/dev-requirements-debian.txt"; then rm -r requirements/dev-requirements-debian.txt; fi
	cp requirements/requirements.txt requirements/dev-requirements.txt
	cp requirements/requirements.txt requirements/dev-requirements-debian.txt
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-requirements.txt requirements/requirements.in requirements/dev-requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-requirements-debian.txt requirements/requirements.in requirements/dev-requirements-debian.in

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
	@while read line; do \
		pip-compile --allow-unsafe --generate-hashes --upgrade-package $file --output-file requirements/dev-requirements-debian.txt requirements/requirements.in requirements/dev-requirements-debian.in; \
	done < 'requirements/dev-requirements-debian.in'

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

.PHONY: version
version:
	@python -c "import securedrop_client; print(securedrop_client.__version__)"

##############
#
# Localization
#
##############

LOCALE_DIR=securedrop_client/locale
LOCALES=$(shell find ${LOCALE_DIR} -name "*.po")
POT=${LOCALE_DIR}/messages.pot
SUPPORTED_LOCALES_LIST=l10n.txt
VERSION=$(shell python -c "import securedrop_client; print(securedrop_client.__version__)")
WEBLATE_API=https://weblate.securedrop.org/api/
WEBLATE_COMPONENT=securedrop-client

.PHONY: check-translation-catalogs
check-translation-catalogs:
	@make update-translation-catalogs
	@git diff --quiet ${LOCALE_DIR} || { echo "Translation catalogs are out of date. Please run \"make update-translation-catalogs\" and commit the changes."; exit 1; }

# Update POTs from translated strings in source code and merge into
# per-locale POs.
.PHONY: update-translation-catalogs
update-translation-catalogs:
	@make --always-make ${POT}
	@for catalog in $$(find ${LOCALE_DIR} -name "*.po"); do make $${catalog}; done

# Compile loadable/packageable MOs.
.PHONY: compile-translation-catalogs
compile-translation-catalogs: ${LOCALE_DIR}/*/LC_MESSAGES/messages.mo
	@for locale in $^; do make $${locale}; done

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

# Merge current POT with a locale's PO.
#
# NB. freedomofpress/securedrop/securedrop/i18n_tool.py updates via
# msgmerge even though pybabel.update() is available.  Here we use
# "pybabel update" for consistency with "pybabel extract".
${LOCALE_DIR}/%/LC_MESSAGES/messages.po: ${POT}
ifeq ($(strip $(LOCALES)),)
	@echo "no translation catalogs to update"
else
	@pybabel update \
		--locale $$(echo $@ | grep -Eio "[a-zA-Z_]+/LC_MESSAGES/messages.po" | sed 's/\/LC_MESSAGES\/messages.po//') \
		--input-file ${POT} \
		--output-file $@ \
		--no-wrap \
		--previous
	@sed -i -e '/^"POT-Creation-Date/d' $@
endif

# Compile a locale's PO to MO for (a) development runtime or (b) packaging.
${LOCALE_DIR}/%/LC_MESSAGES/messages.mo: ${LOCALE_DIR}/%/LC_MESSAGES/messages.po
ifeq ($(strip $(LOCALES)),)
	@echo "no translation catalogs to compile"
else
	@pybabel compile \
		--directory ${LOCALE_DIR} \
		--statistics
endif

# List languages 100% translated in Weblate.
.PHONY: supported-languages
supported-languages:
	@wlc \
		--format json \
		--url ${WEBLATE_API} \
		list-translations \
		| jq -r 'map(select(.component.slug == "${WEBLATE_COMPONENT}" and .translated_percent == 100)) | map("* \(.language.name|tostring) (``\(.translated_percent|tostring)``)") | join("\n")' \
		> ${SUPPORTED_LOCALES_LIST}
	@git add ${SUPPORTED_LOCALES_LIST}
