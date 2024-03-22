.PHONY: all
all: help

.PHONY: build-debs
build-debs: OUT:=build/securedrop-client-$(shell date +%Y%m%d).log
build-debs: ## Build Debian packages
	@echo "Building SecureDrop Client Debian packages..."
	@export TERM=dumb
	@script \
		--command scripts/build-debs.sh --return \
		$(OUT)
	@echo
	@echo "You can now examine or commit the log at:"
	@echo "$(OUT)"

.PHONY: lint-desktop
lint-desktop: ## Lint .desktop files
	# See: https://www.freedesktop.org/wiki/Software/desktop-file-utils/
	find . -name *.desktop -type f -not -path '*/\.git/*' | xargs desktop-file-validate

.PHONY: lint
lint: check-ruff shellcheck ## Run linters and formatters

.PHONY: fix
fix: ## Fix lint and formatting issues
	poetry run ruff format .
	poetry run ruff check . --fix

.PHONY: check-ruff
check-ruff:
	poetry run ruff format . --diff
	poetry run ruff check . --output-format=full

safety:  ## Run safety dependency checks on build dependencies
	find . -name build-requirements.txt | xargs -n1 poetry run safety check --full-report \
		--ignore 51668 \
		--ignore 61601 \
		--ignore 61893 \
		--ignore 62044 \
 		-r

.PHONY: shellcheck
shellcheck:  ## Lint shell scripts
	@poetry run ./scripts/shellcheck.sh

.PHONY: rust-lint
rust-lint: ## Lint Rust code
	cargo fmt --check
	cargo clippy

.PHONY: rust-test
rust-test: ## Run Rust tests
	cargo test

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
