.PHONY: all
all: help

.PHONY: safety
safety: ## Runs `safety check` to check python dependencies for vulnerabilities
	@echo "Running safety against build requirements…"
	@poetry run safety check --full-report -r build-requirements.txt

.PHONY: check
check: lint mypy semgrep test check-black ## Run linter and tests

.PHONY: check-black
check-black: ## Check Python source code formatting with black
	@poetry run black --check --diff ./

TESTS ?= tests
.PHONY: test
test:  ## Run tests
	poetry run pytest -v --cov-report html --cov-report term-missing \
		--cov=securedrop_export --log-disable=securedrop_export.main $$TESTS

.PHONY: lint
lint:  ## Run linter
	poetry run flake8 securedrop_export/ tests/

.PHONY: mypy
mypy:  ## Type check Python files
	poetry run mypy .

.PHONY: black
black: ## Format Python source code with black
	@poetry run black ./

SEMGREP_FLAGS := --exclude "tests/" --error --strict --verbose

.PHONY: semgrep
semgrep:semgrep-community semgrep-local

.PHONY: semgrep-community
semgrep-community:
	@echo "Running semgrep with semgrep.dev community rules..."
	@poetry run semgrep $(SEMGREP_FLAGS) --config "p/r2c-security-audit" --config "p/r2c-ci"

.PHONY: semgrep-local
semgrep-local:
	@echo "Running semgrep with local rules..."
	@poetry run semgrep $(SEMGREP_FLAGS) --config ".semgrep"

# Explanation of the below shell command should it ever break.
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
