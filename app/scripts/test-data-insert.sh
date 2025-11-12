#!/bin/bash

# Check if ./src/test-data.sql exists
if [ ! -f ./src/test-data.sql ]; then
  echo "./src/test-data.sql does not exist."
  echo "Run \`pnpm test-data-generate\` first to generate it."
  exit 1
fi

pnpm run dbmate up
sqlite3 "$HOME/.config/SecureDrop/db.sqlite" < ./src/test-data.sql

# Write journalist pubkey
cp "./src/main/__tests__/files/securedrop.gpg.pub.asc" "$HOME/.config/SecureDrop/public.key"
