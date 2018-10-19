DEFAULT_GOAL: help
OPEN=$(word 1, $(wildcard /usr/bin/xdg-open /usr/bin/open))

.PHONY: format
format: ## Run the formatter
	@docker build -t securedrop-sdk/black:latest -f Dockerfile.black . && \
		docker run --rm -v $(PWD):/home/kdas/workplace securedrop-sdk/black:latest black .

TESTS ?= tests
.PHONY: test
test: ## Run the test suite
	@pipenv run python -m pytest -v --cov sdclientapi --cov-report html --cov-report term-missing $(TESTS)

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
