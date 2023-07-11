.PHONY: all
all: help

VERSION_CODENAME ?= bullseye

.PHONY: venv
venv:  ## Provision a Python 3 virtualenv for **development**
	python3 -m venv .venv
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r requirements/dev-${VERSION_CODENAME}-requirements.txt

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	pip install --upgrade safety && \
		for req_file in `find . -type f -name '*requirements.txt'`; do \
			echo "Checking file $$req_file" \
			&& safety check --full-report -r $$req_file \
			&& echo -e '\n' \
			|| exit 1; \
		done

# Helper, not to be used directly
.PHONY: sync-requirements
sync-requirements:  ## Update dev-requirements.txt to pin to the same versions of prod dependencies
	if test -f "requirements/dev-bullseye-requirements.txt"; then rm -r requirements/dev-bullseye-requirements.txt; fi
	if test -f "requirements/dev-bookworm-requirements.txt"; then rm -r requirements/dev-bookworm-requirements.txt; fi
	$(MAKE) dev-requirements

# Helper, not to be used directly
.PHONY: dev-requirements
dev-requirements:  ## Update dev-*requirements.txt files if pinned versions do not comply with the dependency specifications in dev-*requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-bullseye-requirements.txt requirements/dev-bullseye-requirements.in
	pip-compile --allow-unsafe --generate-hashes --output-file requirements/dev-bookworm-requirements.txt requirements/dev-bookworm-requirements.in

.PHONY: requirements
requirements:  ## Update *requirements.txt files if pinned versions do not comply with the dependency specifications in *requirements.in
	pip-compile --generate-hashes --output-file requirements/requirements.txt requirements/requirements.in
	$(MAKE) dev-requirements

.PHONY: update-dependency
update-dependency:  ## Add or upgrade a package to the latest version that complies with the dependency specifications in requirements.in
	pip-compile --generate-hashes --upgrade-package $(PACKAGE) --output-file requirements/requirements.txt requirements/requirements.in
	$(MAKE) sync-requirements

.PHONY: update-dev-only-dependencies
update-dev-only-dependencies:  ## Update dev-requirements.txt to pin to the latest versions of dev-only dependencies that comply with the dependency specifications in dev-requirements.in
	$(MAKE) sync-requirements
	@while read line; do \
		pip-compile --allow-unsafe --generate-hashes --upgrade-package $file --output-file requirements/dev-bullseye-requirements.txt requirements/dev-bullseye-requirements.in; \
	done < 'requirements/dev-bullseye-requirements.in'
	@while read line; do \
		pip-compile --allow-unsafe --generate-hashes --upgrade-package $file --output-file requirements/dev-bookworm-requirements.txt requirements/dev-bookworm-requirements.in; \
	done < 'requirements/dev-bookworm-requirements.in'

.PHONY: check
check: lint mypy semgrep test check-black ## Run linter and tests

.PHONY: check-black
check-black: ## Check Python source code formatting with black
	@black --check --diff ./

TESTS ?= tests
.PHONY: test
test:  ## Run tests
	pytest -v --cov-report html --cov-report term-missing --cov=securedrop_export $$TESTS

.PHONY: lint
lint:  ## Run linter
	flake8 securedrop_export/ tests/

.PHONY: mypy
mypy:  ## Type check Python files
	mypy .

.PHONY: black
black: ## Format Python source code with black
	@black ./

SEMGREP_FLAGS := --exclude "tests/" --error --strict --verbose

.PHONY: semgrep
semgrep:semgrep-community semgrep-local

.PHONY: semgrep-community
semgrep-community:
	@echo "Running semgrep with semgrep.dev community rules..."
	@semgrep $(SEMGREP_FLAGS) --config "p/r2c-security-audit" --config "p/r2c-ci"

.PHONY: semgrep-local
semgrep-local:
	@echo "Running semgrep with local rules..."
	@semgrep $(SEMGREP_FLAGS) --config ".semgrep"

# Explaination of the below shell command should it ever break.
# 1. Set the field separator to ": ##" and any make targets that might appear between : and ##
# 2. Use sed-like syntax to remove the make targets
# 3. Format the split fields into $$1) the target name (in blue) and $$2) the target descrption
# 4. Pass this file as an arg to awk
# 5. Sort it alphabetically
# 6. Format columns with colon as delimiter.
.PHONY: help
help: ## Print this message and exit.
	@printf "Makefile for developing and testing the SecureDrop export code.\n"
	@printf "Subcommands:\n"
	@awk 'BEGIN {FS = ":.*?## "} /^[0-9a-zA-Z_-]+:.*?## / {printf "\033[36m%s\033[0m : %s\n", $$1, $$2}' $(MAKEFILE_LIST) \
		| sort \
| column -s ':' -t
