# Bandit is a static code analysis tool to detect security vulnerabilities in Python applications
# https://wiki.openstack.org/wiki/Security/Projects/Bandit
.PHONY: all
all: help

.PHONY: venv
venv:
	python3 -m venv .venv ## Provision a Python 3 virtualenv for **development**
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r "requirements/dev-requirements.txt"

.PHONY: bandit
bandit: ## Run bandit with medium level excluding test-related folders
	pip install --upgrade pip && \
		pip install --upgrade bandit!=1.6.0 && \
	bandit -ll --recursive securedrop_proxy

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	pip install --upgrade safety && \
		for req_file in `find . -type f -name '*requirements.txt'`; do \
			echo "Checking file $$req_file" \
			&& safety check --full-report -r $$req_file \
			&& echo -e '\n' \
			|| exit 1; \
		done

.PHONY: lint
lint: isort-check black-check ## Run isort, black and flake8
	@flake8 securedrop_proxy tests

.PHONY: mypy
mypy: ## Run mypy static type checker
	@mypy --ignore-missing-imports securedrop_proxy

.PHONY: black
black: ## Run black for file formatting
	@black securedrop_proxy tests

.PHONY: black-check
black-check: ## Check Python source code formatting with black
	@black --check --diff securedrop_proxy tests

.PHONY: isort
isort: ## Run isort for file formatting
	@isort securedrop_proxy/*.py tests/*.py

.PHONY: isort-check
isort-check: ## Check isort for file formatting
	@isort --check-only --diff securedrop_proxy/*.py tests/*.py

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

.PHONY: test
test: clean .coverage ## Runs tests with coverage

.coverage:
	@coverage run --source securedrop_proxy -m unittest

.PHONY: browse-coverage
browse-coverage: .coverage ## Generates and opens HTML coverage report
	@coverage html
	@xdg-open htmlcov/index.html 2>/dev/null || open htmlcov/index.html 2>/dev/null

.PHONY: check
check: clean lint test mypy safety bandit  ## Runs all tests and code checkers

.PHONY: clean
clean:  ## Clean the workspace of generated resources
	@rm -rf .mypy_cache build dist *.egg-info .coverage .eggs docs/_build .pytest_cache lib htmlcov .cache && \
		find . \( -name '*.py[co]' -o -name dropin.cache \) -delete && \
		find . \( -name '*.bak' -o -name dropin.cache \) -delete && \
		find . \( -name '*.tgz' -o -name dropin.cache \) -delete && \
		find . -name __pycache__ -print0 | xargs -0 rm -rf

# Explanation of the below shell command should it ever break.
# 1. Set the field separator to ": ##" and any make targets that might appear between : and ##
# 2. Use sed-like syntax to remove the make targets
# 3. Format the split fields into $$1) the target name (in blue) and $$2) the target descrption
# 4. Pass this file as an arg to awk
# 5. Sort it alphabetically
# 6. Format columns with colon as delimiter.
.PHONY: help
help: ## Print this message and exit.
	@printf "Makefile for developing and testing the SecureDrop proxy.\n"
	@printf "Subcommands:\n\n"
	@awk 'BEGIN {FS = ":.*?## "} /^[0-9a-zA-Z_-]+:.*?## / {printf "\033[36m%s\033[0m : %s\n", $$1, $$2}' $(MAKEFILE_LIST) \
		| sort \
		| column -s ':' -t
