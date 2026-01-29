.PHONY: all
all: help

.PHONY: build-debs
build-debs: OUT:=build/securedrop-client-$(shell date +%Y%m%d).log
build-debs: ## Build Debian packages
	# "build-debs.sh" will create this directory, but we need it to exist
	# before we call "script".
	@mkdir -p build
	@echo "Building SecureDrop Client Debian packages..."
	@export TERM=dumb
	@script \
		--command scripts/build-debs.sh --return \
		$(OUT)
	@echo
	@echo "You can now examine or commit the log at:"
	@echo "$(OUT)"

.PHONY: build-debs-app
build-debs-app: OUT:=build/securedrop-app-$(shell date +%Y%m%d).log
build-debs-app: ## Build Debian packages, including SecureDrop App
	# "build-debs.sh" will create this directory, but we need it to exist
	# before we call "script".
	@mkdir -p build
	@echo "Building SecureDrop Client Debian packages..."
	@export TERM=dumb
	@script \
		--command bash -c "export WHAT=app; scripts/build-debs.sh" --return \
		$(OUT)
	@echo
	@echo "You can now examine or commit the log at:"
	@echo "$(OUT)"


.PHONY: lint-apparmor
lint-apparmor: ## Lint AppArmor profiles
	# See apparmor_parser(8)
	apparmor_parser --preprocess --abort-on-error --Werror=all client/files/usr.bin.securedrop-client

.PHONY: lint-desktop
lint-desktop: ## Lint .desktop files
	# See: https://www.freedesktop.org/wiki/Software/desktop-file-utils/
	find . -name *.desktop -type f -not -path '*/\.git/*' | xargs desktop-file-validate

.PHONY: lint
lint: check-ruff shellcheck zizmor semgrep ## Run linters and formatters

.PHONY: fix
fix: ## Fix lint and formatting issues
	poetry run ruff format .
	poetry run ruff check . --fix

.PHONY: check-ruff
check-ruff:
	poetry run ruff format . --diff
	poetry run ruff check . --output-format=full

.PHONY: shellcheck
shellcheck:  ## Lint shell scripts
	@poetry run ./scripts/shellcheck.sh

.PHONY: zizmor
zizmor: ## Lint GitHub Actions workflows
	@poetry run zizmor .

.PHONY: semgrep
semgrep: semgrep-app semgrep-client semgrep-export ## Run Semgrep security checks on all components

.PHONY: semgrep-app
semgrep-app: ## Run Semgrep on app/ (JavaScript/TypeScript)
	@echo "Running semgrep on app/ directory..."
	@poetry run semgrep scan --metrics=off \
		--exclude "*test*" \
		--exclude "*__tests__*" \
		--error \
		--strict \
		--verbose \
		--config p/javascript \
		--config p/typescript \
		--config p/react \
		--config p/nodejs \
		--config p/security-audit \
		--config p/ci \
		--config app/.semgrep \
		app/

.PHONY: semgrep-client
semgrep-client: ## Run Semgrep on client/ (Python)
	@echo "Running semgrep on client/ directory..."
	@poetry run semgrep scan --metrics=off \
		--exclude "tests/" \
		--error \
		--strict \
		--verbose \
		--config "p/security-audit" \
		--config "p/ci" \
		--config "client/.semgrep" \
		client/

.PHONY: semgrep-export
semgrep-export: ## Run Semgrep on export/ (Python)
	@echo "Running semgrep on export/ directory..."
	@poetry run semgrep scan --metrics=off \
		--exclude "tests/" \
		--error \
		--strict \
		--verbose \
		--config "p/security-audit" \
		--config "p/ci" \
		--config "export/.semgrep" \
		export/

.PHONY: rust-lint
rust-lint: ## Lint Rust code
	cargo fmt --check
	cargo clippy
	cargo clippy --features qubesdb

.PHONY: rust-test
rust-test: ## Run Rust tests
	cargo test
	cargo test --features qubesdb

.PHONY: install-deps-app
install-deps-app: ## Install dependencies needed to run the Electron app
	# Install nvm and Node v24
	@if [ ! -d "$$HOME/.nvm" ]; then \
		curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.40.3/install.sh | bash; \
	fi
	@export NVM_DIR="$$HOME/.nvm" && . "$$NVM_DIR/nvm.sh" && nvm install 24
	# Install Rust toolchain via rustup
	@if ! command -v rustup > /dev/null 2>&1; then \
		curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y; \
	fi
	@. "$$HOME/.cargo/env" && rustup default stable
	# Install pnpm via npm
	@export NVM_DIR="$$HOME/.nvm" && . "$$NVM_DIR/nvm.sh" && npm install -g pnpm
	# Install system packages
	sudo apt-get update && sudo apt-get install -y jq pkg-config libssl-dev python3 python3-pip
	# Install poetry
	@if ! command -v poetry > /dev/null 2>&1; then \
		pip3 install poetry; \
	fi

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
