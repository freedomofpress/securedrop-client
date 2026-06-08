# SecureDrop Inbox

## Overview

This is an Electron-based desktop application that provides a secure interface for SecureDrop journalists to communicate with sources. The app is built with React, Redux Toolkit, and TypeScript, featuring a modern UI with Ant Design components and Tailwind CSS.

## Prerequisites

- Node.js v24
- Rust toolchain (2021 edition or later; for the proxy component)
- pnpm package manager
- System packages `jq`, `pkg-config`, `sqlite3`, and `openssl`
- Python and [Poetry](https://python-poetry.org/docs/#installing-with-the-official-installer)

On a Debian Bookworm VM, we recommend installing Node and Rust via [nvm](https://github.com/nvm-sh/nvm) and [rustup](https://rustup.rs/), which installs them in your local `PATH`. You can then install `pnpm` via `npm install -g pnpm@latest`.

- [Node.js installation guide](https://nodejs.org/en/download)
- [Rust installation guide](https://www.rust-lang.org/tools/install)

## Quick Start

### 1. Install System Packages

Install the required system packages (`jq`, `pkg-config`, `openssl`, `python3`, `sqlite3`, and Electron dependencies):

```bash
sudo apt-get update && sudo apt-get install -y \
    jq pkg-config libssl-dev python3 python3-pip pipx \
    libglib2.0-0 libnspr4 libnss3 libdbus-1-3 libatk1.0-0 libatk-bridge2.0-0 \
    libcups2 libcairo2 libgtk-3-0 libgbm1 libasound2 xvfb sqlite3
```

### 2. Install Dependencies

From the repository root, install Node, Rust, pnpm, and Poetry automatically:

```bash
make install-deps-app
```

Then install the Inbox's Node dependencies:

```bash
pnpm install
```

### 3. Start Development Inbox Locally

#### Run Inbox Against Local SecureDrop Server

To run against a local SecureDrop server, first follow the instructions to [run the SecureDrop server in localdev](https://github.com/freedomofpress/securedrop?tab=readme-ov-file#developer-quickstart).

Once the server has been started, you can build and start the Inbox in development mode with:

```bash
pnpm dev
```

This will:

- Build the SecureDrop proxy component (requires Rust)
- Configure environment variables automatically
- Start the Inbox in development mode

To enable autologin, run with:

```bash
pnpm dev -- --login
```

If you are running on Qubes OS, you will need to pass in the `--no-qubes` flag in localdev. This ensures the Inbox
loads development configuration rather than attempting to read config values from QubesDB as expected in the production Qubes Workstation environment.

```bash
pnpm dev -- --no-qubes
```

#### Run Inbox Against Demo SecureDrop Server

To run the Inbox against the [Demo SecureDrop instance](https://demo.securedrop.org/), start it with:

```bash
pnpm dev-demo
```

This will start the Inbox with autologin against the demo SecureDrop instance.

You can then access the [Demo Source Interface](https://demo-source.securedrop.org/) to test sending new submissions and reading replies.

### 4. Available Scripts

- `pnpm dev` - Start in development mode
- `pnpm start` - Start in production mode
- `pnpm test` - Run unit tests with coverage
- `pnpm integration-test` - Run integration tests
- `pnpm build` - Build for production
- `pnpm build:linux` - Build Linux distribution package
- `pnpm lint` - Check code style and linting
- `pnpm fix` - Auto-fix linting and formatting issues
- `pnpm typecheck` - Run TypeScript type checking
- `pnpm test-data-generate` - Generate random test data into `src/test-data.sql`
- `pnpm test-data-insert` - Insert the test data into the database

## Development

### Project Structure

```
src/
├── main/           # Electron main process
│   ├── database/   # SQLite database and migrations
│   ├── proxy.ts    # Integration with SecureDrop proxy
│   └── index.ts    # Main process entry point
├── preload/        # Electron preload scripts
└── renderer/       # React frontend application
    ├── features/   # Redux slices and business logic
    ├── views/      # Page components (SignIn, Inbox)
    └── App.tsx     # Main application component
```

### Testing

Run the test suite:

```bash
# Unit tests
pnpm test

# Integration tests
pnpm integration-test

# Type checking
pnpm typecheck
```

#### Server tests

Ensure that you have a SecureDrop server development environment set up in the folder `../securedrop`. The server tests will start this server for you.

Run the server tests:

```
pnpm server-test
```

### Database

The Inbox uses SQLite with migrations managed by dbmate:

```bash
# Run database migrations
pnpm dbmate up

# Create new migration
pnpm dbmate new migration_name
```

### Using a proxy VM

The production environment (`pnpm start`) will attempt to use a proxy VM.

The VM in which you are running the Inbox must have RPC policy access to the proxy VM. When using `sd-proxy`, this is configured in `dom0` in the file `/etc/qubes/policy.d/31-securedrop-workstation.policy`.

## License

AGPL-3.0-or-later
