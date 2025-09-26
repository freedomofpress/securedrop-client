# SecureDrop App

A pre-alpha re-implementation of the SecureDrop Client for Qubes, built with modern web technologies.

**NOTE:** This project is not yet ready for production use. Please see the [`client`](../client) directory for the implementation currently in use in production.

## Overview

This is an Electron-based desktop application that provides a secure interface for SecureDrop journalists to communicate with sources. The app is built with React, Redux Toolkit, and TypeScript, featuring a modern UI with Ant Design components and Tailwind CSS.

## Prerequisites

- Node.js (v22 or later)
- Rust toolchain (2021 edition or later; for the proxy component)
- pnpm package manager
- System packages `jq` and `pkg-config`

On a Debian Bookworm VM, we recommend installing Node and Rust via [nvm](https://github.com/nvm-sh/nvm) and [rustup](https://rustup.rs/), which installs them in your local `PATH`. You can then install `pnpm` via `npm install -g pnpm@latest`.

- [Node.js installation guide](https://nodejs.org/en/download)
- [Rust installation guide](https://www.rust-lang.org/tools/install)

## Quick Start

### 1. Install Dependencies

```bash
pnpm install
```

### 2. Generate and Insert Test Data

In order to see sources in the interface, you need to generate test data and insert it. The `test-data-generate` script requires that you pass in the path to the `securedrop` repo, and the number of sources you want to generate.

```bash
pnpm test-data-generate ../../securedrop 1000
pnpm test-data-insert
```

### 3. Start Development Server

```bash
pnpm dev
```

This will:

- Build the SecureDrop proxy component (requires Rust)
- Configure environment variables automatically
- Start the Electron app in development mode

### 3. Available Scripts

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

Once you have a SecureDrop server development environment set up, start the server
using our fixed dataset:

```
USE_FIXED_DATA="../securedrop-client/app/server_tests/data/data.yaml" make dev
```

Once it's started, you can run:

```
pnpm server-test
```

### Database

The app uses SQLite with migrations managed by dbmate:

```bash
# Run database migrations
pnpm dbmate up

# Create new migration
pnpm dbmate new migration_name
```

### Using a proxy VM

The production environment (`pnpm start`) will attempt to use a proxy VM.

The VM in which you are running the app must have RPC policy access to the proxy VM. When using `sd-proxy`, this is configured in `dom0` in the file `/etc/qubes/policy.d/31-securedrop-workstation.policy`.

## License

AGPL-3.0-or-later

## Contributing

This is pre-alpha software under active development. Please refer to the main SecureDrop project documentation for contribution guidelines.
