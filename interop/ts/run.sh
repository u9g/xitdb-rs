#!/bin/sh
# Replicates databases between this crate and the TypeScript implementation
# (the `xitdb` npm package, github.com/xit-vcs/xitdb-ts), the way a server
# keeps in-memory replicas in browser clients in sync:
#
#   * rust writes a history with every data type, and a new ts replica gets
#     a full copy, then a delta per transaction
#   * the ts replica sends its ReplicaState, and rust sends what it missed
#   * ts rejects a delta that doesn't start at its committed size, or that
#     comes from another file, and re-syncs
#   * rust compacts the database, and ts gets a full copy of the new file
#   * both compute the same trailer checksums
#   * rust replicates a database written by ts
#
# examples/ts_replication.rs drives it; client.ts is the ts side.
# Requires cargo, and node 22.18+ (which runs TypeScript directly) with pnpm or npm.
set -eu

cd "$(dirname "$0")"
if command -v pnpm >/dev/null 2>&1; then
    pnpm install --silent --frozen-lockfile
else
    npm install --silent --no-package-lock
fi
cargo run --quiet --example ts_replication -- node client.ts
