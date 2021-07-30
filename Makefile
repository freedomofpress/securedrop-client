DEFAULT_GOAL: help
OPEN=$(word 1, $(wildcard /usr/bin/xdg-open /usr/bin/open))

.PHONY: venv
venv:  ## Provision a Python 3 virtualenv for **development**
	python3 -m venv .venv
	## Good idea to upgrade pip and wheel when you create a new dev virtual environment.
	## Or you could use the virtualenv command instead.
	.venv/bin/pip install --upgrade pip wheel
	.venv/bin/pip install --require-hashes -r dev-requirements.txt

.PHONY: black
black: ## Format Python source code with black
	@black setup.py sdclientapi tests

.PHONY: check-black
check-black: ## Check Python source code formatting with black
	@black --check --diff setup.py sdclientapi tests

.PHONY: isort
isort: ## Run isort to organize Python imports
	@isort --recursive setup.py sdclientapi tests

.PHONY: check-isort
check-isort: ## Check Python import organization with isort
	@isort --check-only --diff --recursive setup.py sdclientapi tests

TESTS ?= tests
.PHONY: test
test: ## Run the test suite
	@python -m pytest -v --cov sdclientapi --cov-report html --cov-report term-missing $(TESTS)

.PHONY: lint
lint: ## Run the flake8 lints
	@flake8 sdclientapi tests

.PHONY: mypy
mypy: ## Run the mypy typechecker
	@mypy sdclientapi

.PHONY: check
check: check-black check-isort lint mypy safety test ## Run all checks and tests

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	pip install --upgrade safety && \
		for req_file in `find . -type f -name '*requirements.txt'`; do \
			echo "Checking file $$req_file" \
			&& safety check --full-report -r $$req_file \
			&& echo -e '\n' \
			|| exit 1; \
		done

.PHONY: update-pip-requirements
update-pip-requirements: ## Updates all Python requirements files via pip-compile.
	pip-compile --generate-hashes --output-file dev-requirements.txt requirements.in dev-requirements.in
	pip-compile --generate-hashes --output-file requirements.txt requirements.in

.PHONY: open-coverage-report
open-coverage-report: ## Open the coverage report in your browser
	@$(OPEN) htmlcov/index.html

# Explaination of the below shell command should it ever break.
# 1. Set the field separator to ": ##" and any make targets that might appear between : and ##
# 2. Use sed-like syntax to remove the make targets
# 3. Format the split fields into $$1) the target name (in blue) and $$2) the target descrption
# 4. Pass this file as an arg to awk
# 5. Sort it alphabetically
# 6. Format columns with colon as delimiter.
.PHONY: help
help: ## Print this message and exit.
	@printf "Makefile for developing and testing the SecureDrop SDK.\n"
	@printf "Subcommands:\n\n"
	@awk 'BEGIN {FS = ":.*?## "} /^[0-9a-zA-Z_-]+:.*?## / {printf "\033[36m%s\033[0m : %s\n", $$1, $$2}' $(MAKEFILE_LIST) \
		| sort \
		| column -s ':' -t
