# Bandit is a static code analysis tool to detect security vulnerabilities in Python applications
# https://wiki.openstack.org/wiki/Security/Projects/Bandit
.PHONY: all
all: help

.PHONY: lint
lint: mypy ## Run flake8 and mypy
	@poetry run flake8 securedrop_proxy tests

.PHONY: mypy
mypy: ## Run mypy static type checker
	@poetry run mypy --ignore-missing-imports securedrop_proxy

.PHONY: test
test: ## Runs tests with pytest
	@poetry run pytest

.PHONY: check
check: lint test mypy ## Runs all tests and code checkers

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
