#!/usr/bin/env bash 

set -eo pipefail 
umask 077

echo "Building proxy..."
make -C ../proxy build

function configure_environment() {
    echo "Configuring .env.local..."

    # Configure Vite environment variables
    # Accessible in the code as import.meta.env.VITE_ENV_VAR
    # See: https://vite.dev/guide/env-and-mode
    LOCAL_DOTENV_FILE=".env.local"
    : > "$LOCAL_DOTENV_FILE"

    sd_proxy_cmd="$(cargo metadata --format-version 1 | jq -r '.target_directory')/debug/securedrop-proxy"

    ENV_VARS=(
        "VITE_SD_PROXY_ORIGIN=\"http://localhost:8081/\""
        "VITE_SD_PROXY_CMD=\"$sd_proxy_cmd\""
    )

    for var in "${ENV_VARS[@]}"; do 
        echo "$var" >> "$LOCAL_DOTENV_FILE"
    done
}

configure_environment

electron-vite dev
