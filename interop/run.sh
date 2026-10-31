#!/bin/sh
# Round-trips a database between this crate and the Go implementation
# (github.com/xit-vcs/xitdb-go), to check that they share a file format:
#
#   1. rust writes a database with every data type
#   2. go verifies it and appends a moment
#   3. rust verifies go's moment and compacts the database
#   4. go verifies the compacted copy
#
# Requires cargo and go (1.23+).
set -eu

cd "$(dirname "$0")"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT

cargo run --quiet --example interop -- write "$dir/main.db"
go run . append "$dir/main.db"
cargo run --quiet --example interop -- verify "$dir/main.db"
cargo run --quiet --example interop -- compact "$dir/main.db" "$dir/compact.db"
go run . verify "$dir/compact.db"
echo "interop: ok"
